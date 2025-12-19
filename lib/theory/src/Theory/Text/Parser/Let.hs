-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Portability : portable
--
-- Parsing protocol theories. See the MANUAL for a high-level description of
-- the syntax.

module Theory.Text.Parser.Let(
    letBlock
  , genericletBlock
)
where

import Term.Substitution
import Theory.Text.Parser.Token
import Text.Parsec
import Theory.Text.Parser.Term

-- | Parse a let block with bottom-up application semantics.
genericletBlock :: Parser a1 -> Parser a2 -> Parser [(a1, a2)]
genericletBlock varp termp = many1 definition
    where
        definition = (,) <$> (varp <* equalSign) <*> termp

letBlock :: Parser LNSubst
letBlock = do
        _  <- letIdentifier
        -- Be careful when adding additional sorts: LSortMsg has an empty prefix and should be last in the list.
        -- Generally: No sort prefix (suffix) should be a PREFIX of a sort prefix (suffix) later in the list.
        ls <-genericletBlock (sortedLVar [LSortG, LSortE, LSortNat, LSortMsg]) (msetterm False llit) -- TODO: Might need to add more DH sorts here
        _  <- symbol "in"
        return $ toSubst ls
  where
    toSubst = foldr1 compose . map (substFromList . return)
