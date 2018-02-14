{-# LANGUAGE OverloadedStrings #-}

module IRTS.IL.Gen.Source (
    Indentable(..),
    Source,
    Line,
    buildSource,
    line,
    text
) where

import Data.Monoid
import Data.String
import qualified Data.Text as T

--
--
--

class Indentable a where
    indent :: Int -> a -> a

--
--
--

newtype Source = Source {
    getSource :: [Line]
}

instance Monoid Source where
    mempty = Source []
    mappend (Source lx) (Source rx) = Source (lx <> rx)

instance Indentable Source where
    indent n = Source . fmap (indent n) . getSource

newtype Line = Line {
    unLine :: T.Text
}

instance Monoid Line where
    mempty = Line ""
    mappend (Line l) (Line r) = Line (l <> r)

instance Indentable Line where
    indent n = Line . (T.replicate n " " <>) . unLine

instance IsString Line where
    fromString = Line . T.pack

--
--
--

buildSource :: Source -> T.Text
buildSource = T.intercalate "\n" . fmap unLine . getSource

line :: Line -> Source
line = Source . pure

text :: T.Text -> Line
text = Line
