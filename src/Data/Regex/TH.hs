{-# LANGUAGE TemplateHaskell #-}
-- | Quasi-quoters for doing pattern matching using tree regular expressions.
module Data.Regex.TH (rx, mrx) where

import Data.Regex.Generics
import qualified Data.Regex.MultiGenerics as M
import qualified Language.Haskell.Exts as E
import Language.Haskell.Exts.Parser
import Language.Haskell.Meta.Syntax.Translate
import Language.Haskell.TH
import Language.Haskell.TH.Quote

rPat :: String -> Q Pat
rPat s = case parseExp ("(" ++ s ++ ")") of
           ParseFailed _ msg -> fail msg
           ParseOk expr -> do eName <- getFreeVars (getUnboundVarsE expr)
                              let nullSrc  = E.SrcLoc "" 0 0
                                  fullExpr = E.App (E.Con (E.Qual (E.ModuleName "Data.Regex.Generics") (E.Ident "Regex"))) expr
                              case eName of
                                []  -> return $ ViewP (AppE (VarE 'with)
                                                            (toExp fullExpr))
                                                      (ConP 'Just [ConP '() []])
                                [v] -> return $ ViewP (AppE (VarE 'with)
                                                            (toExp $ E.Lambda nullSrc [toIntegerVar v] fullExpr))
                                                      (ConP 'Just [toPat (E.PVar v)])
                                vs  -> return $ ViewP (AppE (VarE 'with)
                                                            (toExp $ E.Lambda nullSrc (map toIntegerVar vs) fullExpr))
                                                      (ConP 'Just [TupP $ map (toPat . E.PVar) vs])

getUnboundVarsE :: E.Exp -> [E.Name]
getUnboundVarsE (E.Var (E.UnQual n)) = [n]
getUnboundVarsE (E.Var _)            = []
getUnboundVarsE (E.App e1 e2)        = getUnboundVarsE e1 ++ getUnboundVarsE e2
getUnboundVarsE (E.InfixApp e1 _ e2) = getUnboundVarsE e1 ++ getUnboundVarsE e2
getUnboundVarsE (E.LeftSection e _)  = getUnboundVarsE e
getUnboundVarsE (E.RightSection _ e) = getUnboundVarsE e
getUnboundVarsE (E.Paren e)          = getUnboundVarsE e
getUnboundVarsE (E.Lambda _ p e)     = let pvars = map (\(E.PVar n) -> n) p
                                        in filter (not . flip elem pvars) (getUnboundVarsE e)
getUnboundVarsE _                    = []

getFreeVars :: [E.Name] -> Q [E.Name]
getFreeVars []                 = return []
getFreeVars (n@(E.Ident i):ns) = do nRest <- getFreeVars ns
                                    l <- lookupValueName i
                                    case l of
                                      Nothing -> return (n:nRest)
                                      Just _  -> return nRest
getFreeVars (_:ns)             = getFreeVars ns

toIntegerVar :: E.Name -> E.Pat
toIntegerVar e = E.PatTypeSig (E.SrcLoc "" 0 0)
                              (E.PVar e)
                              (E.TyCon (E.Qual (E.ModuleName "Prelude") (E.Ident "Integer")))

-- | Builds a pattern for a matching a tree regular expression over
--   a regular data type. Those variables not bound are taken to be
--   capture identifiers. Note that the value of capture identifiers
--   is always a list, even if it matches only one subterm in the
--   given tree regular expression.
--
--   One example of use is:
--
--   > f [rx| iter $ \k -> x <<- inj One <||> y <<- inj (Two (k#)) |] =
--   >   ... x and y available here with type [Fix f] ...
--
--   In many cases, it is useful to define pattern synonyms for
--   injecting constructors, as shown below:
--
--   > pattern One_   = Inject One
--   > pattern Two_ x = Inject (Two_ x)
--   > 
--   > f [rx| (\k -> x <<- One_ <||> y <<- Two_ (k#))^* |] = ...
rx :: QuasiQuoter
rx = QuasiQuoter { quotePat  = rPat
                 , quoteExp  = fail "Quasi-quoter only supports patterns"
                 , quoteType = fail "Quasi-quoter only supports patterns"
                 , quoteDec  = fail "Quasi-quoter only supports patterns"
                 }

mrPat :: String -> Q Pat
mrPat s = case parseExp ("(" ++ s ++ ")") of
            ParseFailed _ msg -> fail msg
            ParseOk expr -> do let (newExpr, unbound) = getUnboundVarsM expr
                               eName <- getFreeVarsM unbound
                               let nullSrc  = E.SrcLoc "" 0 0
                                   fullExpr = E.App (E.Con (E.Qual (E.ModuleName "Data.Regex.MultiGenerics") (E.Ident "Regex"))) newExpr
                               case eName of
                                 []  -> return $ ViewP (AppE (VarE 'M.with)
                                                             (toExp fullExpr))
                                                       (ConP 'Just [ConP '() []])
                                 [(v,ty)] -> return $ ViewP (AppE (VarE 'M.with)
                                                                  (toExp $ E.Lambda nullSrc [toVarM (v,ty)] fullExpr))
                                                            (ConP 'Just [toPat (E.PVar v)])
                                 vs  -> return $ ViewP (AppE (VarE 'M.with)
                                                             (toExp $ E.Lambda nullSrc (map toVarM vs) fullExpr))
                                                       (ConP 'Just [TupP $ map (toPat . E.PVar . fst) vs])

getUnboundVarsM :: E.Exp -> (E.Exp, [(E.Name, E.Type)])
getUnboundVarsM (E.ExpTypeSig _ v@(E.Var (E.UnQual n)) ty) = (v, [(n,ty)])
getUnboundVarsM v@(E.Var _)          = (v, [])
getUnboundVarsM (E.App e1 e2)        = let (r1, m1) = getUnboundVarsM e1
                                           (r2, m2) = getUnboundVarsM e2
                                        in (E.App r1 r2, m1 ++ m2)
getUnboundVarsM (E.InfixApp e1 o e2) = let (r1, m1) = getUnboundVarsM e1
                                           (r2, m2) = getUnboundVarsM e2
                                        in (E.InfixApp r1 o r2, m1 ++ m2)
getUnboundVarsM (E.LeftSection e o)  = let (r,m) = getUnboundVarsM e
                                        in (E.LeftSection r o, m)
getUnboundVarsM (E.RightSection o e) = let (r,m) = getUnboundVarsM e
                                        in (E.RightSection o r, m)
getUnboundVarsM (E.Paren e)          = let (r,m) = getUnboundVarsM e
                                        in (E.Paren r, m)
getUnboundVarsM (E.Lambda l p e)     = let pvars = map (\(E.PVar n) -> n) p
                                           (r,m) = getUnboundVarsM e
                                        in (E.Lambda l p r, filter (not . flip elem pvars . fst) m)
getUnboundVarsM x                    = (x, [])

getFreeVarsM :: [(E.Name, E.Type)] -> Q [(E.Name, E.Type)]
getFreeVarsM []                     = return []
getFreeVarsM ((n@(E.Ident i),t):ns) = do nRest <- getFreeVarsM ns
                                         l <- lookupValueName i
                                         case l of
                                           Nothing -> return ((n,t):nRest)
                                           Just _  -> return nRest
getFreeVarsM (_:ns)                 = getFreeVarsM ns

toVarM :: (E.Name, E.Type) -> E.Pat
toVarM (e,ty) = E.PatTypeSig (E.SrcLoc "" 0 0)
                             (E.PVar e)
                             (E.TyApp (E.TyApp (E.TyCon (E.Qual (E.ModuleName "Data.Regex.MultiGenerics") (E.Symbol "Wrap")))
                                               (E.TyCon (E.Qual (E.ModuleName "Prelude") (E.Ident "Integer"))))
                                      ty)

-- | Builds a pattern for a matching a tree regular expression over
--   a family of regular data type. Those variables not bound are
--   taken to be capture identifiers, and their index should be explicitly
--   given in the expression. Note that the value of capture identifiers
--   is always a list, even if it matches only one subterm in the
--   given tree regular expression.
--
--   One example of use is:
--
--   > f [mrx| iter $ \k -> (x :: A) <<- inj One <||> (y :: B) <<- inj (Two (k#)) |] =
--   >   ... x is available with type [Fix f A]
--   >   ... and y with type [Fix f B]
mrx :: QuasiQuoter
mrx = QuasiQuoter { quotePat  = mrPat
                  , quoteExp  = fail "Quasi-quoter only supports patterns"
                  , quoteType = fail "Quasi-quoter only supports patterns"
                  , quoteDec  = fail "Quasi-quoter only supports patterns"
                  }
