{-# LANGUAGE OverloadedStrings #-}

module IRTS.IL.Gen (
    generateIL
) where

import IRTS.IL.Gen.Source

import IRTS.CodegenCommon
import IRTS.Lang
import IRTS.Simplified
import Idris.Core.TT

import Control.Monad (forM_, when)
import Control.Monad.RWS hiding (local)
import Control.Monad.State
import Data.Char (ord)
import Data.List (intersperse, nub)
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.String (fromString)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Numeric (showFFloat)

className :: Line
className = "IDR"

--
--
--

type Gen' = RWS FuncInf FuncDef GenState
type Gen = Gen' ()

data FuncInf = FuncInf {
    funcName :: String,
    argCount :: Int
}

data GenState = GenState {
    uniq :: Int,
    depth :: Int
}

data FuncDef = FuncDef {
    funcLocals :: [Int],
    funcSource :: Source
}

instance Monoid FuncDef where
    mempty = FuncDef mempty mempty
    mappend (FuncDef l1 s1) (FuncDef l2 s2) = FuncDef (l1 <> l2) (s1 <> s2)

emit :: Source -> Gen
emit s = do
    GenState _ depth <- get
    (tell . FuncDef []) (indent depth s)

regLocal :: Int -> Gen
regLocal = tell . flip FuncDef mempty . pure

indentG :: Gen
indentG = modify incDepth
    where
    incDepth s = s { depth = depth s + 2 }

unindentG :: Gen
unindentG = modify incDepth
    where
    incDepth s = s { depth = depth s - 2 }

--
--
--

generateIL :: CodeGenerator
generateIL i = do
    let st = GenState 65537 0
    let emitted = (mconcat . runGen st) $ mapM (genFn . snd) (simpleDecls i)
    let source = preamble <> indent 2 emitted <> postamble
    T.writeFile (outputFile i) (buildSource source)
    where
    runGen st = flip evalState st

preamble :: Source
preamble =
    line ".assembly extern mscorlib {}" <>
    line ".assembly I {}" <>
    line (".class private sealed beforefieldinit " <> className) <>
    lbrace

postamble :: Source
postamble = rbrace

--
--
--

genFn :: SDecl -> State GenState Source
genFn (SFun n args i def) = do
    st <- get
    let inf = FuncInf (showCG n) (length args)
    let entry = n == entryPointName
    let runGen m = execRWS m inf st
    let (st', FuncDef lx src) = runGen (indentG *> genExpr def *> (if entry then pop else emit mempty) *> ret *> unindentG)
    put st'
    (pure . mconcat) [
            genFnDecl n args,
            lbrace,
            if entry then line ".entrypoint" else mempty,
            (indent 2 . mconcat) (local <$> nub lx),
            src,
            rbrace,
            line ""
        ]

genFnDecl :: Name -> [Name] -> Source
genFnDecl n args = line decl
    where
    rt = if n == MN 0 "runMain" then "void" else "object"
    decl = mconcat [
            ".method static assembly ",
            rt,
            " ",
            name n,
            argsTP args,
            " cil managed"
        ]

argsTP :: [Name] -> Line
argsTP args = "(" <> joinWith ", " (fmap argName args) <> ")"
    where argName = ("object " <>) . name

entryPointName :: Name
entryPointName = MN 0 "runMain"

--
--
--

genExpr :: SExp -> Gen
genExpr (SV v) = genSV v
genExpr (SApp tcall f args) = genApp tcall f args
genExpr (SLet (Loc i) e ex) = genLet i e ex
genExpr (SUpdate v e) = genExpr e
genExpr (SCon _ i n args) = genCon i n args
genExpr (SCase _ v alts) = genCase v alts
genExpr (SChkCase v alts) = genCase v alts
genExpr (SProj v i) = throw "SProj"
genExpr (SConst c) = genConst c
genExpr (SForeign d1 d2 ax) = throw "FFI unsupported"
genExpr (SOp f args) = genOp args f
genExpr (SError e) = throw e
genExpr SNothing = throw "SNothing"

--
--
--

genSV :: LVar -> Gen
genSV = loadVar

--
--
--

genApp :: Bool -> Name -> [LVar] -> Gen
genApp tcall f args = do
    mapM_ loadVar args
    -- when tcall tailc --TODO: impl
    callFn Call Stat "object" className (name f) (const "object" <$> args)

--
--
--

genLet :: Int -> SExp -> SExp -> Gen
genLet i v ex = do
    regLocal i
    loadV
    stloc i
    genExpr ex
    where
    loadV = case v of
        SNothing -> ldnull
        _ -> genExpr v

--
--
--

genCon :: Int -> Name -> [LVar] -> Gen
genCon i n args = do
    GenState arrix d <- get
    put (GenState (arrix + 1) d)
    regLocal arrix
    ldc_i4 (length args + 1)
    newarr "object"
    stloc arrix
    ldloc arrix
    ldc_i4 0
    ldc_i4 i
    box_i4
    stelem "object"
    mapM_ (uncurry $ pushToArray arrix) (zip [1..] args)
    ldloc arrix
    where
    pushToArray arrix ix arg = do
        ldloc arrix
        ldc_i4 ix
        loadVar arg
        stelem "object"

--
--
--

genCase :: LVar -> [SAlt] -> Gen
genCase v alts = do
    slabel <- genLabel
    elabel <- genLabel
    br slabel
    cases <- mapM (genAlt elabel v) alts
    label slabel
    mapM_ (uncurry $ compAndBranch v) cases
    ldnull
    label elabel

compAndBranch :: LVar -> VComp -> Line -> Gen
compAndBranch v (Direct c) clabel = do
    comp v c
    beq clabel
compAndBranch v (Tag t) clabel = do
    loadCon v
    ldc_i4 0
    ldelem "object"
    unbox_i4
    ldind_i4
    ldc_i4 t
    beq clabel
compAndBranch _ Default clabel = do
    br clabel

comp :: LVar -> Const -> Gen
comp v (I v') = do
    loadVar v
    unbox_i4
    ldind_i4
    ldc_i4 (fromIntegral v')
comp v (BI v') = do
    loadVar v
    unbox_i8
    ldind_i8
    ldc_i8 v'
comp v (Fl v') = do
    loadVar v
    unbox_r8
    ldind_r8
    ldc_r8 v'
comp v (Ch v') = do
    loadVar v
    unbox_i4
    ldind_i4
    ldc_i4 (ord v')
comp v (Str v') = do
    loadVar v
    ldstr v'
comp v (B8 v') = do
    loadVar v
    unbox_i4
    ldind_i4
    ldc_i4 (fromIntegral v')
comp v (B16 v') = do
    loadVar v
    unbox_i4
    ldind_i4
    ldc_i4 (fromIntegral v')
comp v (B32 v') = do
    loadVar v
    unbox_i4
    ldind_i4
    ldc_i4 (fromIntegral v')
comp v (B64 v') = do
    loadVar v
    unbox_i8
    ldind_i8
    ldc_i8 (fromIntegral v')
comp v c = throw ("Unsupported const " <> show c)

isConCase :: SAlt -> Bool
isConCase (SConCase _ _ _ _ _) = True
isConCase _ = False

genAlt :: Line -> LVar -> SAlt -> Gen' (VComp, Line)
genAlt elabel _ (SConstCase c ex) = do
    alabel <- genLabel
    emitBranch alabel
    pure (Direct c, alabel)
    where
    emitBranch alabel = do
        label alabel
        genExpr ex
        br elabel
genAlt elabel con (SConCase lv t n args ex) = do
    alabel <- genLabel
    emitBranch alabel
    pure (Tag t, alabel)
    where
    emitBranch alabel = do
        let ixx = fst <$> zip (zip [lv..] [1..]) args
        label alabel
        forM_ ixx $ \(locix, arrix) -> do
            regLocal locix
            loadCon con
            ldc_i4 arrix
            ldelem "object"
            stloc locix
        genExpr ex
        br elabel
genAlt elabel con (SDefaultCase ex) = do
    alabel <- genLabel
    emitBranch alabel
    pure (Default, alabel)
    where
    emitBranch alabel = do
        label alabel
        genExpr ex
        br elabel

loadCon :: LVar -> Gen
loadCon v = do
    loadVar v
    castclass "class [mscorlib]System.Object[]"

data VComp
    = Direct Const
    | Tag Int
    | Default

--
--
--

genConst :: Const -> Gen
genConst (I v) = do
    ldc_i4 (fromIntegral v)
    box_i4
genConst (BI v) = do
    ldc_i8 (fromIntegral v)
    box_i8
genConst (Fl v) = do
    ldc_r8 v
    box_r8
genConst (Ch v) = do
    ldc_i4 (ord v)
    box_i4
genConst (Str v) = do
    ldstr v
genConst (B8 v) = do
    ldc_i4 (fromIntegral v)
    box_i4
genConst (B16 v) = do
    ldc_i4 (fromIntegral v)
    box_i4
genConst (B32 v) = do
    ldc_i4 (fromIntegral v)
    box_i4
genConst (B64 v) = do
    ldc_i8 (fromIntegral v)
    box_i8
genConst c = throw ("Unsupported const " <> show c)
{--
genConst (AType v)
genConst StrType
genConst WorldType
genConst TheWorld
genConst VoidType
genConst Forgot
--}

--
--
--

genOp :: [LVar] -> PrimFn -> Gen
genOp args (LPlus typ) = genPrimOp "add" typ Nothing args
genOp args (LMinus typ) = genPrimOp "sub" typ Nothing args
genOp args (LTimes typ) = genPrimOp "mul" typ Nothing args
genOp args (LUDiv typ) = genPrimOp "div.un" (ATInt typ) Nothing args
genOp args (LSDiv typ) = genPrimOp "div" typ Nothing args
genOp args (LURem typ) = genPrimOp "rem.un" (ATInt typ) Nothing args
genOp args (LSRem typ) = genPrimOp "rem" typ Nothing args
genOp args (LAnd typ) = genPrimOp "and" (ATInt typ) Nothing args
genOp args (LOr typ) = genPrimOp "or" (ATInt typ) Nothing args
genOp args (LXOr typ) = genPrimOp "xor" (ATInt typ) Nothing args
genOp args (LCompl typ) = genPrimOp "not" (ATInt typ) Nothing args
genOp args (LSHL typ) = genPrimOp "shl" (ATInt typ) Nothing args
genOp args (LLSHR typ) = genPrimOp "shr.un" (ATInt typ) Nothing args
genOp args (LASHR typ) = genPrimOp "shr" (ATInt typ) Nothing args
genOp args (LEq typ) = genPrimOp "ceq" typ (Just box_i4) args
genOp args (LLt typ) = genPrimOp "clt" (ATInt typ) (Just box_i4) args
genOp args (LLe typ) = genLE (ATInt typ) args
genOp args (LGt typ) = genPrimOp "cgt" (ATInt typ) (Just box_i4) args
genOp args (LGe typ) = genGE (ATInt typ) args
genOp args (LSLt typ) = genPrimOp "clt" typ (Just box_i4) args
genOp args (LSLe typ) = genLE typ args
genOp args (LSGt typ) = genPrimOp "cgt" typ (Just box_i4) args
genOp args (LSGe typ) = genGE typ args
genOp [a] (LSExt _ _) = loadVar a
genOp [a] (LZExt _ _) = loadVar a
genOp [a] (LTrunc _ _) = loadVar a
genOp args LStrConcat = do
    mapM_ loadVar args
    callFn Call Stat "string" "[mscorlib]System.String" "Concat" ["string", "string"]
genOp args LStrLt = do
    mapM_ loadVar args
    callFn Call Inst "int32" "[mscorlib]System.String" "CompareTo" ["string"]
    ldc_i4 0
    clt
    box_i4
genOp args LStrEq = do
    mapM_ loadVar args
    callFn Call Stat "bool" "[mscorlib]System.String" "op_Equality" ["string", "string"]
    box_i4
genOp [s] LStrLen = do
    loadVar s
    castclass "[mscorlib]System.String"
    callFn VCall Inst "int32" "[mscorlib]System.String" "get_Length" []
    box_i4
genOp [s] LStrHead = do
    loadVar s
    castclass "[mscorlib]System.String"
    ldc_i4 0
    callFn Call Inst "char" "[mscorlib]System.String" "get_Chars" ["int32"]
    conv_i4
    box_i4
genOp [s] LStrTail = do
    loadVar s
    castclass "[mscorlib]System.String"
    ldc_i4 1
    callFn Call Inst "string" "[mscorlib]System.String" "Substring" ["int32"]
genOp [a, ax] LStrCons = do
    loadVar a
    unbox_i4
    ldind_i4
    callFn Call Stat "char" "[mscorlib]System.Convert" "ToChar" ["int32"]
    callFn Call Stat "string" "[mscorlib]System.Char" "ToString" ["char"]
    loadVar ax
    castclass "[mscorlib]System.String"
    callFn Call Stat "string" "[mscorlib]System.String" "Concat" ["string", "string"]
genOp [s, ix] LStrIndex = do
    loadVar s
    castclass "[mscorlib]System.String"
    loadVar ix
    unbox_i4
    callFn VCall Inst "char" "[mscorlib]System.String" "get_Chars" ["int32"]
    conv_i4
    box_i4
genOp [s] LStrRev = do
    loadVar s
    castclass "[mscorlib]System.String"
    callFn VCall Inst "char[]" "[mscorlib]System.String" "ToCharArray" []
    dup
    callFn Call Stat "void" "[mscorlib]System.Array" "Reverse" ["char[]"]
    newobj "[mscorlib]System.String" ["char[]"]
genOp [ix, c, s] LStrSubstr = do
    loadVar s
    castclass "[mscorlib]System.String"
    loadVar ix
    unbox_i4
    loadVar c
    unbox_i4
    callFn Call Inst "string" "[mscorlib]System.String" "Substring" ["int32", "int32"]
genOp [i] (LIntFloat typ) = genPrimCast (cilUnbox $ ATInt typ) (conv_r8 *> box_r8) i
genOp [i] (LFloatInt typ) = genPrimCast unbox_r8 (cilConv (ATInt typ) *> cilBox (ATInt typ)) i
genOp [i] (LIntStr typ) = genPrimToString (ATInt typ) i
genOp [i] (LStrInt typ) = genPrimRead (ATInt typ) i
genOp [i] LFloatStr = genPrimToString ATFloat i
genOp [i] LStrFloat = genPrimRead ATFloat i
genOp [i] (LChInt typ) = genPrimCast unbox_i4 (cilConv (ATInt typ) *> cilBox (ATInt typ)) i
genOp [i] (LIntCh typ) = genPrimCast (cilUnbox $ ATInt typ) (conv_i4 *> box_i4) i
genOp [_, s] LWriteStr = do
    loadVar s
    castclass "[mscorlib]System.String"
    callFn Call Stat "void" "[mscorlib]System.Console" "Write" ["string"]
    ldnull
genOp args op = throw ("Unsupported primop: " <> show (args, op))
{--
genOp args LFExp
genOp args LFLog
genOp args LFSin
genOp args LFCos
genOp args LFTan
genOp args LFASin
genOp args LFACos
genOp args LFATan
genOp args LFATan2
genOp args LFSqrt
genOp args LFFloor
genOp args LFCeil
genOp args LFNegate
genOp args LReadStr
genOp args LNoOp
genOp args LSystemInfo
genOp args LFork
genOp args LPar
genOp args (LExternal Name)
genOp args LCrash
--}

genPrimOp :: Line -> ArithTy -> Maybe Gen -> [LVar] -> Gen
genPrimOp op ty boxt args = do
    forM_ args $ \arg -> do
        loadVar arg
        cilUnbox ty
    emit (line op)
    maybe (cilBox ty) id boxt

genLE :: ArithTy -> [LVar] -> Gen
genLE = genOrdE "clt"

genGE :: ArithTy -> [LVar] -> Gen
genGE = genOrdE "cgt"

genOrdE :: Line -> ArithTy -> [LVar] -> Gen
genOrdE cmp ty args = do
    mlabel <- genLabel
    genPrimOp cmp ty (Just box_i4) args
    unbox_i4
    brtrue mlabel
    genPrimOp "ceq" ty (Just box_i4) args
    unbox_i4
    brtrue mlabel
    ldc_i4 0
    box_i4
    ret
    label mlabel
    ldc_i4 1
    box_i4
    ret

genPrimCast :: Gen -> Gen -> LVar -> Gen
genPrimCast unbox convAndBox i = do
    loadVar i
    unbox
    convAndBox

genPrimToString :: ArithTy -> LVar -> Gen
genPrimToString ty i = do
    loadVar i
    cilUnbox ty
    callFn Call Inst "string" (cilType ty) "ToString" []

genPrimRead :: ArithTy -> LVar -> Gen
genPrimRead ty i = throw ("Unimplemented: prim read: " <> show (ty, i))

cilBox :: ArithTy -> Gen
cilBox ATFloat = box_r8
cilBox (ATInt (ITFixed IT8)) = box_i4
cilBox (ATInt (ITFixed IT16)) = box_i4
cilBox (ATInt (ITFixed IT32)) = box_i4
cilBox (ATInt (ITFixed IT64)) = box_i8
cilBox (ATInt ITNative) = box_i8
cilBox (ATInt ITBig) = box_i8
cilBox (ATInt ITChar) = box_i4

cilUnbox :: ArithTy -> Gen
cilUnbox ATFloat = unbox_r8
cilUnbox (ATInt (ITFixed IT8)) = unbox_i4
cilUnbox (ATInt (ITFixed IT16)) = unbox_i4
cilUnbox (ATInt (ITFixed IT32)) = unbox_i4
cilUnbox (ATInt (ITFixed IT64)) = unbox_i8
cilUnbox (ATInt ITNative) = unbox_i4
cilUnbox (ATInt ITBig) = unbox_i8
cilUnbox (ATInt ITChar) = unbox_i4

cilConv :: ArithTy -> Gen
cilConv ATFloat = conv_r8
cilConv (ATInt (ITFixed IT8)) = conv_i4
cilConv (ATInt (ITFixed IT16)) = conv_i4
cilConv (ATInt (ITFixed IT32)) = conv_i4
cilConv (ATInt (ITFixed IT64)) = conv_i8
cilConv (ATInt ITNative) = conv_i8
cilConv (ATInt ITBig) = conv_i8
cilConv (ATInt ITChar) = conv_i4

cilType :: ArithTy -> Line
cilType ATFloat = "[mscorlib]System.Double"
cilType (ATInt (ITFixed IT8)) = "[mscorlib]System.Int32"
cilType (ATInt (ITFixed IT16)) = "[mscorlib]System.Int32"
cilType (ATInt (ITFixed IT32)) = "[mscorlib]System.Int32"
cilType (ATInt (ITFixed IT64)) = "[mscorlib]System.Int64"
cilType (ATInt ITNative) = "[mscorlib]System.Int32"
cilType (ATInt ITBig) = "[mscorlib]System.Int64"
cilType (ATInt ITChar) = "[mscorlib]System.Int32"

--
--
--

loadVar :: LVar -> Gen
loadVar (Glob n) = throw ("Unsupported: " <> show (Glob n))
loadVar (Loc i) = do
    FuncInf _ n <- ask
    case n > i of
        True -> ldarg i
        False -> ldloc i

genLabel :: Gen' Line
genLabel = do
    GenState ix depth <- get
    put (GenState (ix + 1) depth)
    pure ("label" <> fromString (show ix))

genAuxLocal :: Gen' Int
genAuxLocal = do
    GenState ix d <- get
    put (GenState (ix + 1) d)
    regLocal ix
    pure ix

callFn :: CallType -> CallCtx -> Line -> Line -> Line -> [Line] -> Gen
callFn ctyp cctx rtyp cls mthd args = (emit . line) (preamble <> mthd <> argst)
    where
    preamble = c <> md <> rtyp <> " " <> cls <> "::"
    c = if ctyp == Call then "call " else "callvirt "
    md = if cctx == Inst then "instance " else ""
    argst = "(" <> joinWith "," args <> ")"

data CallType
    = Call
    | VCall
    deriving Eq

data CallCtx
    = Inst
    | Stat
    deriving Eq

--
--
--

pop :: Gen
pop = emit (line "pop")

ldarg :: Int -> Gen
ldarg = (emit . line) . ("ldarg " <>) . fromString . show

ldstr :: String -> Gen
ldstr = (emit . line) . ("ldstr " <>) . fromString . show

ldc_i4 :: Int -> Gen
ldc_i4 = (emit . line) . ("ldc.i4 " <>) . fromString . show

ldc_i8 :: Integer -> Gen
ldc_i8 = (emit . line) . ("ldc.i8 " <>) . fromString . show

ldc_r8 :: Double -> Gen
ldc_r8 = (emit . line) . ("ldc.r8 " <>) . fromString . ($ "") . showFFloat Nothing

ldnull :: Gen
ldnull = (emit . line) "ldnull"

box_i4 :: Gen
box_i4 = (emit . line) "box int32"

unbox_i4 :: Gen
unbox_i4 = (emit . line) "unbox int32"

ldind_i4 :: Gen
ldind_i4 = (emit . line) "ldind.i4"

conv_i4 :: Gen
conv_i4 = (emit . line) "conv.i4"

box_i8 :: Gen
box_i8 = (emit . line) "box int64"

unbox_i8 :: Gen
unbox_i8 = (emit . line) "unbox int64"

ldind_i8 :: Gen
ldind_i8 = (emit . line) "ldind.i8"

conv_i8 :: Gen
conv_i8 = (emit . line) "conv.i8"

box_r8 :: Gen
box_r8 = (emit . line) "box double"

unbox_r8 :: Gen
unbox_r8 = (emit . line) "unbox double"

ldind_r8 :: Gen
ldind_r8 = (emit . line) "ldind.r8"

conv_r8 :: Gen
conv_r8 = (emit . line) "conv.r8"

box_char :: Gen
box_char = (emit . line) "box char"

unbox_char :: Gen
unbox_char = (emit . line) "box char"

local :: Int -> Source
local i = line (".locals init (object loc" <> fromString (show i) <> ")")

stloc :: Int -> Gen
stloc i = (emit . line) ("stloc loc" <> fromString (show i))

ldloc :: Int -> Gen
ldloc i = (emit . line) ("ldloc loc" <> fromString (show i))

tailc :: Gen
tailc = (emit . line) "tail."

ret :: Gen
ret = (emit . line) "ret"

clt :: Gen
clt = emit (line "clt")

cgt :: Gen
cgt = emit (line "cgt")

br :: Line -> Gen
br l = (emit . line) ("br " <> l)

beq :: Line -> Gen
beq l = (emit . line) ("beq " <> l)

brtrue :: Line -> Gen
brtrue l = (emit . line) ("brtrue " <> l)

label :: Line -> Gen
label l = do
    unindentG
    (emit . line) (l <> ":")
    indentG

dup :: Gen
dup = emit (line "dup")

castclass :: Line -> Gen
castclass = emit . line . ("castclass " <>)

newarr :: Line -> Gen
newarr = emit . line . ("newarr " <>)

stelem :: Line -> Gen
stelem = emit . line . ("stelem " <>)

ldelem :: Line -> Gen
ldelem = emit . line . ("ldelem " <>)

newobj :: Line -> [Line] -> Gen
newobj typ args = (emit . line) ("newobj instance void " <> typ <> "::.ctor" <> "(" <> ax <> ")")
    where ax = joinWith "," args

throw :: String -> Gen
throw e = do
    ldstr e
    newobj "[mscorlib]System.Exception" []
    (emit . line) "throw"
    ldnull

--
--
--

name :: Name -> Line
name = fromString . quote . T.unpack . showName
    where
    quote = ("'" <>) . (<> "'") . mconcat . fmap escape
    escape '\'' = "\\'"
    escape c = pure c

showName :: Name -> T.Text
showName (NS n ns) = T.intercalate "." . reverse $ showName n : ns
showName (UN t) = t
showName (MN i t) = T.concat [t, T.pack $ show i]
showName (SN sn) = T.pack $ show sn
showName e = error ("Unsupported name `" <> show e <> "'")

lbrace :: Source
lbrace = line "{"

rbrace :: Source
rbrace = line "}"

joinWith :: Line -> [Line] -> Line
joinWith t = mconcat . intersperse t
