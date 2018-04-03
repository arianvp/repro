{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE FunctionalDependencies #-}
module Minimal where

import GHC.TypeLits (TypeError, ErrorMessage (..))
import Data.Proxy

data Nat = S Nat | Z
  deriving (Eq , Show)

data SNat :: Nat -> * where
  SZ ::           SNat Z
  SS :: SNat n -> SNat (S n)

type family Lkup (n :: Nat) (ks :: [k]) :: k where
  Lkup Z     (k : ks) = k
  Lkup (S n) (k : ks) = Lkup n ks
  Lkup _     '[]      = TypeError (Text "Lkup index too big")

data El :: [*] -> Nat -> * where
  El ::  {unEl :: Lkup ix fam} -> El fam ix

data NS :: (k -> *) -> [k] -> * where
  T :: NS p xs -> NS p (x : xs)
  H  :: p x     -> NS p (x : xs)

infixr 5 :*
data NP :: (k -> *) -> [k] -> * where
  NP0  :: NP p '[]
  (:*) :: p x -> NP p xs -> NP p (x : xs)

data Atom kon
  = K kon
  | I Nat
  deriving (Eq, Show)

data NA  :: (kon -> *) -> (Nat -> *) -> Atom kon -> * where
  NA_I :: phi k -> NA ki phi (I k) 
  NA_K :: ki  k -> NA ki phi (K k)

data Kon
  = KInt
  | KInteger
  | KFloat
  | KDouble
  | KBool
  | KChar
  | KString
  deriving (Eq , Show)


data Singl (kon :: Kon) :: * where
  SInt     :: Int     -> Singl KInt
  SInteger :: Integer -> Singl KInteger
  SFloat   :: Float   -> Singl KFloat
  SDouble  :: Double  -> Singl KDouble
  SBool    :: Bool    -> Singl KBool
  SChar    :: Char    -> Singl KChar
  SString  :: String  -> Singl KString

deriving instance Show (Singl k)
deriving instance Eq   (Singl k)

eqSingl :: Singl k -> Singl k -> Bool
eqSingl = (==)

class Family (ki :: kon -> *) (fam :: [*]) (codes :: [[[Atom kon]]])
      | fam -> ki codes , ki codes -> fam
  where
    sto'   :: SNat ix -> Rep ki (El fam) (Lkup ix codes) -> ()


newtype Rep (ki :: kon -> *) (phi :: Nat -> *) (code :: [[Atom kon]])
  = Rep { unRep :: NS (PoA ki phi) code }

type PoA (ki :: kon -> *) (phi :: Nat -> *) = NP (NA ki phi)


type FamGoSource =
    '[(), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (),
      (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (),
      (), (), (), (), (), (), (), (), (), (), (), (), ()] 

type CodesGoSource =
    '[ '[ '[I (S Z), I (S (S Z)), I (S (S (S Z)))]],
      '[ '[K KString]],
      '[ '[], '[I (S (S (S (S Z)))), I (S (S Z))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S Z))))))))), I (S (S (S Z)))]],
      '[ '[I (S (S (S (S (S Z)))))]],
      '[ '[], '[I (S (S (S (S (S (S Z)))))), I (S (S (S (S (S Z)))))]],
      '[ '[I (S (S (S (S (S (S (S Z))))))), K KString]],
      '[ '[], '[I (S (S (S (S (S (S (S (S Z))))))))], '[I (S Z)]],
      '[ '[K KString]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S Z))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S Z))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S Z))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))]],
      '[ '[I (S Z),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))),
          I (S Z),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))]],
      '[ '[],
        '[I (S Z),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))),
          I (S Z)],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S Z)))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S Z)))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))]],
      '[ '[], '[], '[]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))),
          I (S Z)],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))),
          I (S Z)],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))),
          I (S Z)],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))),
          K KBool]],
      '[ '[K KString, K KInteger],
        '[K KString, K KFloat],
        '[K KString, K KFloat],
        '[K KString, K KChar],
        '[K KString, K KString],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))]],
      '[ '[K KBool,
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[I (S Z)],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))],
        '[]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S Z)))))))))],
        '[I (S Z),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))],
        '[I (S Z)],
        '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))),
          I (S (S (S (S (S (S (S (S Z)))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))]],
      '[ '[], '[I (S Z)]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))),
          I (S (S (S (S (S (S (S (S Z))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))]],
      '[ '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[I (S Z),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))],
        '[I (S Z)]],
      '[ '[K KString,
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))],
        '[K KString,
          K KBool,
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))]],
      '[ '[I (S Z),
          I (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))]]]
instance Family Singl FamGoSource CodesGoSource where
  sto'
    = \case 
        SZ
          -> \case 
               Rep (H ((NA_I (El y_aj1F)) :* ((NA_I (El y_aj1G)) :* ((NA_I (El y_aj1H)) :* NP0))))
                 -> ()
        SS SZ
          -> \case 
               Rep (H ((NA_K (SString y_aj1I)) :* NP0)) -> ()
        SS (SS SZ)
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj1J)) :* ((NA_I (El y_aj1K)) :* NP0))))
                 -> ()
        SS (SS (SS SZ))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj1L)) :* ((NA_I (El y_aj1M)) :* NP0))))
                 -> ()
        SS (SS (SS (SS SZ)))
          -> \case 
               Rep (H ((NA_I (El y_aj1N)) :* NP0))
                 -> ()
        SS (SS (SS (SS (SS SZ))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj1O)) :* ((NA_I (El y_aj1P)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS SZ)))))
          -> \case 
               Rep (H ((NA_I (El y_aj1Q)) :* ((NA_K (SString y_aj1R)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS SZ))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj1S)) :* NP0)))
                 -> ()
               Rep (T (T (H ((NA_I (El y_aj1T)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))
          -> \case 
               Rep (H ((NA_K (SString y_aj1U)) :* NP0)) -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj1V)) :* NP0)) -> ()
               Rep (T (H ((NA_I (El y_aj1W)) :* NP0)))
                 -> ()
               Rep (T (T (H ((NA_I (El y_aj1X)) :* NP0))))
                 -> ()
               Rep (T (T (T (H ((NA_I (El y_aj1Y)) :* NP0)))))
                 -> ()
               Rep (T (T (T (T (H ((NA_I (El y_aj1Z)) :* NP0))))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj20)) :* ((NA_I (El y_aj21)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj22)) :* ((NA_I (El y_aj23)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj24)) :* ((NA_I (El y_aj25)) :* ((NA_I (El y_aj26)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj27)) :* ((NA_I (El y_aj28)) :* ((NA_I (El y_aj29)) :* ((NA_I (El y_aj2a)) :* NP0)))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj2b)) :* ((NA_I (El y_aj2c)) :* ((NA_I (El y_aj2d)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj2e)) :* ((NA_I (El y_aj2f)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj2g)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj2h)) :* ((NA_I (El y_aj2i)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj2j)) :* ((NA_I (El y_aj2k)) :* NP0)))
                 -> ()
               Rep (T (H ((NA_I (El y_aj2l)) :* ((NA_I (El y_aj2m)) :* NP0))))
                 -> ()
               Rep (T (T (H ((NA_I (El y_aj2n)) :* ((NA_I (El y_aj2o)) :* NP0)))))
                 -> ()
               Rep (T (T (T (H ((NA_I (El y_aj2p)) :* NP0)))))
                 -> ()
               Rep (T (T (T (T (H ((NA_I (El y_aj2q)) :* NP0))))))
                 -> ()
               Rep (T (T (T (T (T (H ((NA_I (El y_aj2r)) :* NP0)))))))
                 -> ()
               Rep (T (T (T (T (T (T (H ((NA_I (El y_aj2s)) :* ((NA_I (El y_aj2t)) :* NP0)))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (H ((NA_I (El y_aj2u)) :* NP0)))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (H ((NA_I (El y_aj2v)) :* NP0))))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (T (H ((NA_I (El y_aj2w)) :* NP0)))))))))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj2x)) :* NP0)) -> ()
               Rep (T (H ((NA_I (El y_aj2y)) :* ((NA_I (El y_aj2z)) :* NP0))))
                 -> ()
               Rep (T (T (H ((NA_I (El y_aj2A)) :* ((NA_I (El y_aj2B)) :* ((NA_I (El y_aj2C)) :* NP0))))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H NP0)) -> ()
               Rep (T (T (H NP0))) -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj2D)) :* ((NA_I (El y_aj2E)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj2F)) :* ((NA_I (El y_aj2G)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj2H)) :* ((NA_I (El y_aj2I)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj2J)) :* NP0)) -> ()
               Rep (T (H ((NA_I (El y_aj2K)) :* ((NA_I (El y_aj2L)) :* NP0))))
                 -> ()
               Rep (T (T (H ((NA_I (El y_aj2M)) :* ((NA_I (El y_aj2N)) :* NP0)))))
                 -> ()
               Rep (T (T (T (H ((NA_I (El y_aj2O)) :* NP0)))))
                 -> ()
               Rep (T (T (T (T (H ((NA_I (El y_aj2P)) :* ((NA_I (El y_aj2Q)) :* NP0)))))))
                 -> ()
               Rep (T (T (T (T (T (H ((NA_I (El y_aj2R)) :* NP0)))))))
                 -> ()
               Rep (T (T (T (T (T (T (H ((NA_I (El y_aj2S)) :* ((NA_I (El y_aj2T)) :* NP0)))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (H ((NA_I (El y_aj2U)) :* ((NA_I (El y_aj2V)) :* NP0))))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (H ((NA_I (El y_aj2W)) :* ((NA_I (El y_aj2X)) :* NP0)))))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (T (H ((NA_I (El y_aj2Y)) :* ((NA_I (El y_aj2Z)) :* NP0))))))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (T (T (H ((NA_I (El y_aj30)) :* ((NA_I (El y_aj31)) :* NP0)))))))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (T (T (T (H ((NA_I (El y_aj32)) :* ((NA_I (El y_aj33)) :* ((NA_K (SBool y_aj34)) :* NP0)))))))))))))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_K (SString y_aj35)) :* ((NA_K (SInteger y_aj36)) :* NP0)))
                 -> ()
               Rep (T (H ((NA_K (SString y_aj37)) :* ((NA_K (SFloat y_aj38)) :* NP0))))
                 -> ()
               Rep (T (T (H ((NA_K (SString y_aj39)) :* ((NA_K (SFloat y_aj3a)) :* NP0)))))
                 -> ()
               Rep (T (T (T (H ((NA_K (SString y_aj3b)) :* ((NA_K (SChar y_aj3c)) :* NP0))))))
                 -> ()
               Rep (T (T (T (T (H ((NA_K (SString y_aj3d)) :* ((NA_K (SString y_aj3e)) :* NP0)))))))
                 -> ()
               Rep (T (T (T (T (T (H ((NA_I (El y_aj3f)) :* ((NA_I (El y_aj3g)) :* NP0))))))))
                 -> ()
               Rep (T (T (T (T (T (T (H ((NA_I (El y_aj3h)) :* NP0))))))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_K (SBool y_aj3i)) :* ((NA_I (El y_aj3j)) :* ((NA_I (El y_aj3k)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj3l)) :* NP0)) -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj3m)) :* ((NA_I (El y_aj3n)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj3o)) :* ((NA_I (El y_aj3p)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj3q)) :* ((NA_I (El y_aj3r)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj3s)) :* NP0)))
                 -> ()
               Rep (T (T (H ((NA_I (El y_aj3t)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj3u)) :* NP0)) -> ()
               Rep (T (H ((NA_I (El y_aj3v)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj3w)) :* NP0)) -> ()
               Rep (T (H NP0)) -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj3x)) :* ((NA_I (El y_aj3y)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj3z)) :* ((NA_I (El y_aj3A)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj3B)) :* ((NA_I (El y_aj3C)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj3D)) :* NP0)) -> ()
               Rep (T (H ((NA_I (El y_aj3E)) :* ((NA_I (El y_aj3F)) :* NP0))))
                 -> ()
               Rep (T (T (H ((NA_I (El y_aj3G)) :* NP0))))
                 -> ()
               Rep (T (T (T (H ((NA_I (El y_aj3H)) :* NP0)))))
                 -> ()
               Rep (T (T (T (T (H ((NA_I (El y_aj3I)) :* NP0))))))
                 -> ()
               Rep (T (T (T (T (T (H ((NA_I (El y_aj3J)) :* NP0)))))))
                 -> ()
               Rep (T (T (T (T (T (T (H ((NA_I (El y_aj3K)) :* NP0))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (H ((NA_I (El y_aj3L)) :* NP0)))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (H NP0)))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (T (H ((NA_I (El y_aj3M)) :* NP0)))))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (T (T (H ((NA_I (El y_aj3N)) :* ((NA_I (El y_aj3O)) :* ((NA_I (El y_aj3P)) :* NP0))))))))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (T (T (T (H ((NA_I (El y_aj3Q)) :* NP0)))))))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (H ((NA_I (El y_aj3R)) :* ((NA_I (El y_aj3S)) :* NP0)))))))))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (H ((NA_I (El y_aj3T)) :* ((NA_I (El y_aj3U)) :* ((NA_I (El y_aj3V)) :* NP0)))))))))))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H ((NA_I (El y_aj3W)) :* ((NA_I (El y_aj3X)) :* NP0)))))))))))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H ((NA_I (El y_aj3Y)) :* NP0)))))))))))))))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj3Z)) :* NP0)))
                 -> ()
               Rep (T (T (H ((NA_I (El y_aj40)) :* ((NA_I (El y_aj41)) :* NP0)))))
                 -> ()
               Rep (T (T (T (H ((NA_I (El y_aj42)) :* NP0)))))
                 -> ()
               Rep (T (T (T (T (H ((NA_I (El y_aj43)) :* NP0))))))
                 -> ()
               Rep (T (T (T (T (T (H ((NA_I (El y_aj44)) :* NP0)))))))
                 -> ()
               Rep (T (T (T (T (T (T (H ((NA_I (El y_aj45)) :* ((NA_I (El y_aj46)) :* ((NA_I (El y_aj47)) :* NP0))))))))))
                 -> ()
               Rep (T (T (T (T (T (T (T (H ((NA_I (El y_aj48)) :* ((NA_I (El y_aj49)) :* NP0))))))))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4a)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj4b)) :* ((NA_I (El y_aj4c)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4d)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4e)) :* ((NA_I (El y_aj4f)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4g)) :* ((NA_I (El y_aj4h)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4i)) :* ((NA_I (El y_aj4j)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj4k)) :* NP0)) -> ()
               Rep (T (H ((NA_I (El y_aj4l)) :* ((NA_I (El y_aj4m)) :* ((NA_I (El y_aj4n)) :* NP0)))))
                 -> ()
               Rep (T (T (H ((NA_I (El y_aj4o)) :* ((NA_I (El y_aj4p)) :* NP0)))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4q)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4r)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj4s)) :* ((NA_I (El y_aj4t)) :* NP0)))
                 -> ()
               Rep (T (H ((NA_I (El y_aj4u)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4v)) :* ((NA_I (El y_aj4w)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj4x)) :* ((NA_I (El y_aj4y)) :* NP0)))
                 -> ()
               Rep (T (H ((NA_I (El y_aj4z)) :* ((NA_I (El y_aj4A)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4B)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj4C)) :* ((NA_I (El y_aj4D)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj4E)) :* ((NA_I (El y_aj4F)) :* NP0)))
                 -> ()
               Rep (T (H ((NA_I (El y_aj4G)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj4H)) :* ((NA_I (El y_aj4I)) :* NP0)))
                 -> ()
               Rep (T (H ((NA_I (El y_aj4J)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4K)) :* ((NA_I (El y_aj4L)) :* NP0))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj4M)) :* ((NA_I (El y_aj4N)) :* NP0)))
                 -> ()
               Rep (T (H ((NA_I (El y_aj4O)) :* NP0)))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_K (SString y_aj4P)) :* ((NA_I (El y_aj4Q)) :* ((NA_I (El y_aj4R)) :* NP0))))
                 -> ()
               Rep (T (H ((NA_K (SString y_aj4S)) :* ((NA_K (SBool y_aj4T)) :* ((NA_I (El y_aj4U)) :* NP0)))))
                 -> ()
        SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> \case 
               Rep (H ((NA_I (El y_aj4V)) :* ((NA_I (El y_aj4W)) :* NP0)))
                 -> ()
