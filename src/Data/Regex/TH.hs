{-# LANGUAGE TemplateHaskell #-}
module Data.Regex.TH where

import Data.Regex.Generics
import Language.Haskell.TH

r :: Q Exp -> Q Pat
r e = do v <- e
         case v of
           LamE p _ -> do let bases = map (\x -> case x of VarP n -> nameBase n) p
                          case map (VarP . mkName) bases of
                            []  -> return $ ViewP (AppE (VarE 'with) v)
                                                  (ConP 'Just [ConP '() []])
                            [x] -> return $ ViewP (AppE (VarE 'with) v)
                                                  (ConP 'Just [x])
                            xs  -> return $ ViewP (AppE (VarE 'with) v)
                                                  (ConP 'Just [TupP xs])
           _        -> fail "Not a lambda-expression"
         
