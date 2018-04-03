{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeSynonymInstances   #-}
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



pattern SD0  = SZ
pattern SD1  = SS SZ
pattern SD2  = SS (SS SZ)
pattern SD3  = SS (SS (SS ( SZ)))
pattern SD4  = SS (SS (SS (SS (SZ))))
pattern SD5  = SS (SS (SS (SS (SS (SZ)))))
pattern SD6  = SS (SS (SS (SS (SS (SS (SZ))))))
pattern SD7  = SS (SS (SS (SS (SS (SS (SS (SZ)))))))
pattern SD8  = SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))
pattern SD9  = SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))
pattern SD10 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))
pattern SD11 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))
pattern SD12 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))
pattern SD13 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))
pattern SD14 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))
pattern SD15 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))
pattern SD16 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))
pattern SD17 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))
pattern SD18 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))
pattern SD19 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))
pattern SD20 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))
pattern SD21 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))
pattern SD22 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))
pattern SD23 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))
pattern SD24 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))
pattern SD25 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))
pattern SD26 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))
pattern SD27 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))
pattern SD28 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))
pattern SD29 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))
pattern SD30 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))
pattern SD31 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))
pattern SD32 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))
pattern SD33 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))))
pattern SD34 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))))
pattern SD35 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))))))
pattern SD36 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))))))
pattern SD37 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))))))))
pattern SD38 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))))))))
pattern SD39 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))))))))))
pattern SD40 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))))))))))
pattern SD41 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))))))))))))
pattern SD42 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))))))))))))
pattern SD43 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))))))))))))))
pattern SD44 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))))))))))))))
pattern SD45 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))))))))))))))))
pattern SD46 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))))))))))))))))
pattern SD47 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))))))))))))))))))
pattern SD48 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))))))))))))))))))
pattern SD49 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))))))))))))))))))))
pattern SD50 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))))))))))))))))))))
pattern SD51 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))))))))))))))))))))))
pattern SD52 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern SD53 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern SD54 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern SD55 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern SD56 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern SD57 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern SD58 = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SZ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

type D1  = S Z
type D2  = S (S Z)
type D3  = S (S (S ( Z)))
type D4  = S (S (S (S (Z))))
type D5  = S (S (S (S (S (Z)))))
type D6  = S (S (S (S (S (S (Z))))))
type D7  = S (S (S (S (S (S (S (Z)))))))
type D8  = S (S (S (S (S (S (S (S (Z))))))))
type D9  = S (S (S (S (S (S (S (S (S (Z)))))))))
type D10 = S (S (S (S (S (S (S (S (S (S (Z))))))))))
type D11 = S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))
type D12 = S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))
type D13 = S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))
type D14 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))
type D15 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))
type D16 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))
type D17 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))
type D18 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))
type D19 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))
type D20 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))
type D21 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))
type D22 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))
type D23 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))
type D24 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))
type D25 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))
type D26 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))
type D27 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))
type D28 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))
type D29 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))
type D30 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))
type D31 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))
type D32 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))
type D33 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))))
type D34 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))))
type D35 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))))))
type D36 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))))))
type D37 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))))))))
type D38 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))))))))
type D39 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))))))))))
type D40 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))))))))))
type D41 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))))))))))))
type D42 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))))))))))))
type D43 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))))))))))))))
type D44 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))))))))))))))
type D45 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))))))))))))))))
type D46 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))))))))))))))))
type D47 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))))))))))))))))))
type D48 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))))))))))))))))))
type D49 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))))))))))))))))))))
type D50 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))))))))))))))))))))
type D51 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))))))))))))))))))))))
type D52 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))))))))))))))))))))))
type D53 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))))))))))))))))))))))))
type D54 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))))))))))))))))))))))))
type D55 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))
type D56 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))))))))))))))))))))))))))
type D57 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
type D58 = S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


type FamGoSource =
    '[(), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (),
      (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (),
      (), (), (), (), (), (), (), (), (), (), (), (), ()] 


type CodesGoSource =
    '[ '[ '[I D1, I D2, I D3]],
      '[ '[K KString]],
      '[ '[], '[I D4, I D2]],
      '[ '[],
        '[I D9, I D3]],
      '[ '[I D5]],
      '[ '[], '[I D6, I D5]],
      '[ '[I D7, K KString]],
      '[ '[], '[I D8], '[I D1]],
      '[ '[K KString]],
      '[ '[I D10],
        '[I D11],
        '[I D10],
        '[I D12],
        '[I D13]],
      '[ '[],
        '[I D14,
          I D10]],
      '[ '[],
        '[I D58,
          I D11]],
      '[ '[I D1,
          I D21,
          I D33]],
      '[ '[I D26,
          I D1,
          I D21,
          I D33]],
      '[ '[I D15,
          I D16,
          I D17]],
      '[ '[],
        '[I D1,
          I D15]],
      '[ '[],
        '[I D18]],
      '[ '[],
        '[I D19,
          I D17]],
      '[ '[I D15,
          I D1],
        '[I D19,
          I D18],
        '[I D20,
          I D18],
        '[I D18],
        '[I D21],
        '[I D22],
        '[I D18,
          I D18],
        '[I D18],
        '[I D18],
        '[I D23]],
      '[ '[I D24],
        '[I D8,
          I D19],
        '[I D8,
          I D19,
          I D19]],
      '[ '[], '[], '[]],
      '[ '[I D34,
          I D34]],
      '[ '[],
        '[I D56,
          I D22]],
      '[ '[],
        '[I D57,
          I D23]],
      '[ '[I D25],
        '[I D15,
          I D1],
        '[I D26,
          I D1],
        '[I D19],
        '[I D18,
          I D19],
        '[I D18],
        '[I D18,
          I D17],
        '[I D24,
          I D1],
        '[I D24,
          I D19],
        '[I D24,
          I D17],
        '[I D24,
          I D18],
        '[I D24,
          I D17,
          K KBool]],
      '[ '[K KString, K KInteger],
        '[K KString, K KFloat],
        '[K KString, K KFloat],
        '[K KString, K KChar],
        '[K KString, K KString],
        '[I D18,
          I D27],
        '[I D28]],
      '[ '[K KBool,
          I D39,
          I D18]],
      '[ '[I D29]],
      '[ '[I D21,
          I D33]],
      '[ '[],
        '[I D30,
          I D29]],
      '[ '[I D31,
          I D32]],
      '[ '[],
        '[I D1],
        '[I D19]],
      '[ '[I D19],
        '[I D27]],
      '[ '[I D36],
        '[]],
      '[ '[],
        '[I D35,
          I D34]],
      '[ '[I D15,
          I D18]],
      '[ '[],
        '[I D37,
          I D36]],
      '[ '[I D9],
        '[I D1,
          I D37],
        '[I D38],
        '[I D19],
        '[I D17],
        '[I D39],
        '[I D39],
        '[I D1],
        '[],
        '[I D33],
        '[I D40,
          I D33,
          I D41],
        '[I D42],
        '[I D40,
          I D43],
        '[I D40,
          I D44,
          I D39],
        '[I D45,
          I D33],
        '[I D19]],
      '[ '[],
        '[I D19],
        '[I D19,
          I D19],
        '[I D19],
        '[I D19],
        '[I D19],
        '[I D17,
          I D8,
          I D17],
        '[I D15,
          I D17]],
      '[ '[], '[I D1]],
      '[ '[I D46,
          I D47]],
      '[ '[],
        '[I D37]],
      '[ '[],
        '[I D48,
          I D42]],
      '[ '[],
        '[I D53,
          I D43]],
      '[ '[],
        '[I D54,
          I D44]],
      '[ '[I D19],
        '[I D38,
          I D47,
          I D38],
        '[I D17,
          I D19]],
      '[ '[],
        '[I D38]],
      '[ '[],
        '[I D19]],
      '[ '[I D49,
          I D36],
        '[I D36]],
      '[ '[],
        '[I D50,
          I D49]],
      '[ '[I D51,
          I D19],
        '[I D19,
          I D19]],
      '[ '[],
        '[I D52]],
      '[ '[I D19,
          I D8]],
      '[ '[I D17,
          I D36],
        '[I D36]],
      '[ '[I D55,
          I D36],
        '[I D36]],
      '[ '[],
        '[I D18,
          I D55]],
      '[ '[I D1,
          I D21],
        '[I D1]],
      '[ '[K KString,
          I D15,
          I D18],
        '[K KString,
          K KBool,
          I D18]],
      '[ '[I D1,
          I D18]]]
instance Family Singl FamGoSource CodesGoSource where
  sto'
    = \case 
        SD0
          -> \case 
               Rep (H ((NA_I (El y_aj1F)) :* ((NA_I (El y_aj1G)) :* ((NA_I (El y_aj1H)) :* NP0))))
                 -> ()
        SD1
          -> \case 
               Rep (H ((NA_K (SString y_aj1I)) :* NP0)) -> ()
        SD2
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj1J)) :* ((NA_I (El y_aj1K)) :* NP0))))
                 -> ()
        SD3
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj1L)) :* ((NA_I (El y_aj1M)) :* NP0))))
                 -> ()
        SD4
          -> \case 
               Rep (H ((NA_I (El y_aj1N)) :* NP0))
                 -> ()
        SD5
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj1O)) :* ((NA_I (El y_aj1P)) :* NP0))))
                 -> ()
        SD6
          -> \case 
               Rep (H ((NA_I (El y_aj1Q)) :* ((NA_K (SString y_aj1R)) :* NP0)))
                 -> ()
        SD7
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj1S)) :* NP0)))
                 -> ()
               Rep (T (T (H ((NA_I (El y_aj1T)) :* NP0))))
                 -> ()
        SD8
          -> \case 
               Rep (H ((NA_K (SString y_aj1U)) :* NP0)) -> ()
        SD9
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
        SD10
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj20)) :* ((NA_I (El y_aj21)) :* NP0))))
                 -> ()
        SD11
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj22)) :* ((NA_I (El y_aj23)) :* NP0))))
                 -> ()
        SD12
          -> \case 
               Rep (H ((NA_I (El y_aj24)) :* ((NA_I (El y_aj25)) :* ((NA_I (El y_aj26)) :* NP0))))
                 -> ()
        SD13
          -> \case 
               Rep (H ((NA_I (El y_aj27)) :* ((NA_I (El y_aj28)) :* ((NA_I (El y_aj29)) :* ((NA_I (El y_aj2a)) :* NP0)))))
                 -> ()
        SD14
          -> \case 
               Rep (H ((NA_I (El y_aj2b)) :* ((NA_I (El y_aj2c)) :* ((NA_I (El y_aj2d)) :* NP0))))
                 -> ()
        SD15
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj2e)) :* ((NA_I (El y_aj2f)) :* NP0))))
                 -> ()
        SD16
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj2g)) :* NP0)))
                 -> ()
        SD17
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj2h)) :* ((NA_I (El y_aj2i)) :* NP0))))
                 -> ()
        SD18
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
        SD19
          -> \case 
               Rep (H ((NA_I (El y_aj2x)) :* NP0)) -> ()
               Rep (T (H ((NA_I (El y_aj2y)) :* ((NA_I (El y_aj2z)) :* NP0))))
                 -> ()
               Rep (T (T (H ((NA_I (El y_aj2A)) :* ((NA_I (El y_aj2B)) :* ((NA_I (El y_aj2C)) :* NP0))))))
                 -> ()
        SD20
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H NP0)) -> ()
               Rep (T (T (H NP0))) -> ()
        SD21
          -> \case 
               Rep (H ((NA_I (El y_aj2D)) :* ((NA_I (El y_aj2E)) :* NP0)))
                 -> ()
        SD22
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj2F)) :* ((NA_I (El y_aj2G)) :* NP0))))
                 -> ()
        SD23
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj2H)) :* ((NA_I (El y_aj2I)) :* NP0))))
                 -> ()
        SD24
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
        SD25
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
        SD26
          -> \case 
               Rep (H ((NA_K (SBool y_aj3i)) :* ((NA_I (El y_aj3j)) :* ((NA_I (El y_aj3k)) :* NP0))))
                 -> ()
        SD27
          -> \case 
               Rep (H ((NA_I (El y_aj3l)) :* NP0)) -> ()
        SD28
          -> \case 
               Rep (H ((NA_I (El y_aj3m)) :* ((NA_I (El y_aj3n)) :* NP0)))
                 -> ()
        SD29
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj3o)) :* ((NA_I (El y_aj3p)) :* NP0))))
                 -> ()
        SD30
          -> \case 
               Rep (H ((NA_I (El y_aj3q)) :* ((NA_I (El y_aj3r)) :* NP0)))
                 -> ()
        SD31
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj3s)) :* NP0)))
                 -> ()
               Rep (T (T (H ((NA_I (El y_aj3t)) :* NP0))))
                 -> ()
        SD32
          -> \case 
               Rep (H ((NA_I (El y_aj3u)) :* NP0)) -> ()
               Rep (T (H ((NA_I (El y_aj3v)) :* NP0)))
                 -> ()
        SD33
          -> \case 
               Rep (H ((NA_I (El y_aj3w)) :* NP0)) -> ()
               Rep (T (H NP0)) -> ()
        SD34
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj3x)) :* ((NA_I (El y_aj3y)) :* NP0))))
                 -> ()
        SD35
          -> \case 
               Rep (H ((NA_I (El y_aj3z)) :* ((NA_I (El y_aj3A)) :* NP0)))
                 -> ()
        SD36
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj3B)) :* ((NA_I (El y_aj3C)) :* NP0))))
                 -> ()
        SD37
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
        SD38
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
        SD39
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4a)) :* NP0)))
                 -> ()
        SD40
          -> \case 
               Rep (H ((NA_I (El y_aj4b)) :* ((NA_I (El y_aj4c)) :* NP0)))
                 -> ()
        SD41
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4d)) :* NP0)))
                 -> ()
        SD42
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4e)) :* ((NA_I (El y_aj4f)) :* NP0))))
                 -> ()
        SD43
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4g)) :* ((NA_I (El y_aj4h)) :* NP0))))
                 -> ()
        SD44
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4i)) :* ((NA_I (El y_aj4j)) :* NP0))))
                 -> ()
        SD45
          -> \case 
               Rep (H ((NA_I (El y_aj4k)) :* NP0)) -> ()
               Rep (T (H ((NA_I (El y_aj4l)) :* ((NA_I (El y_aj4m)) :* ((NA_I (El y_aj4n)) :* NP0)))))
                 -> ()
               Rep (T (T (H ((NA_I (El y_aj4o)) :* ((NA_I (El y_aj4p)) :* NP0)))))
                 -> ()
        SD46
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4q)) :* NP0)))
                 -> ()
        SD47
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4r)) :* NP0)))
                 -> ()
        SD48
          -> \case 
               Rep (H ((NA_I (El y_aj4s)) :* ((NA_I (El y_aj4t)) :* NP0)))
                 -> ()
               Rep (T (H ((NA_I (El y_aj4u)) :* NP0)))
                 -> ()
        SD49
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4v)) :* ((NA_I (El y_aj4w)) :* NP0))))
                 -> ()
        SD50
          -> \case 
               Rep (H ((NA_I (El y_aj4x)) :* ((NA_I (El y_aj4y)) :* NP0)))
                 -> ()
               Rep (T (H ((NA_I (El y_aj4z)) :* ((NA_I (El y_aj4A)) :* NP0))))
                 -> ()
        SD51
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4B)) :* NP0)))
                 -> ()
        SD52
          -> \case 
               Rep (H ((NA_I (El y_aj4C)) :* ((NA_I (El y_aj4D)) :* NP0)))
                 -> ()
        SD53
          -> \case 
               Rep (H ((NA_I (El y_aj4E)) :* ((NA_I (El y_aj4F)) :* NP0)))
                 -> ()
               Rep (T (H ((NA_I (El y_aj4G)) :* NP0)))
                 -> ()
        SD54
          -> \case 
               Rep (H ((NA_I (El y_aj4H)) :* ((NA_I (El y_aj4I)) :* NP0)))
                 -> ()
               Rep (T (H ((NA_I (El y_aj4J)) :* NP0)))
                 -> ()
        SD55
          -> \case 
               Rep (H NP0) -> ()
               Rep (T (H ((NA_I (El y_aj4K)) :* ((NA_I (El y_aj4L)) :* NP0))))
                 -> ()
        SD56
          -> \case 
               Rep (H ((NA_I (El y_aj4M)) :* ((NA_I (El y_aj4N)) :* NP0)))
                 -> ()
               Rep (T (H ((NA_I (El y_aj4O)) :* NP0)))
                 -> ()
        SD57
          -> \case 
               Rep (H ((NA_K (SString y_aj4P)) :* ((NA_I (El y_aj4Q)) :* ((NA_I (El y_aj4R)) :* NP0))))
                 -> ()
               Rep (T (H ((NA_K (SString y_aj4S)) :* ((NA_K (SBool y_aj4T)) :* ((NA_I (El y_aj4U)) :* NP0)))))
                 -> ()
        SD58
          -> \case 
               Rep (H ((NA_I (El y_aj4V)) :* ((NA_I (El y_aj4W)) :* NP0)))
                 -> ()
