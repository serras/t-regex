{-# LANGUAGE TemplateHaskell #-}
module Data.Regex.TH where

import Data.Regex.Generics
import qualified Language.Haskell.Exts as E
import Language.Haskell.Exts.Parser
import Language.Haskell.Meta.Syntax.Translate
import Language.Haskell.TH
import Language.Haskell.TH.Quote

rPat :: String -> Q Pat
rPat s = case parseExp s of
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
getUnboundVarsE (E.Lambda _ p e)     = let pvars = map (\(E.PVar n) -> n) p
                                        in filter (not . flip elem pvars) (getUnboundVarsE e)
getUnboundVarsE _                    = fail "Only variables, lambdas and apps are supported"

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

rx :: QuasiQuoter
rx = QuasiQuoter { quotePat  = rPat
                 , quoteExp  = fail "Quasi-quoter only supports patterns"
                 , quoteType = fail "Quasi-quoter only supports patterns"
                 , quoteDec  = fail "Quasi-quoter only supports patterns"
                 }
