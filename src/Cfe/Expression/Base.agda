{-# OPTIONS --without-K --safe #-}

open import Function
open import Relation.Binary
import Relation.Binary.PropositionalEquality as ā”

module Cfe.Expression.Base
  {c ā} (over : Setoid c ā)
  where

open Setoid over renaming (Carrier to C)

open import Cfe.Language over as š
open import Cfe.Language.Construct.Concatenate over renaming (_ā_ to _āā_)
open import Cfe.Language.Construct.Single over
open import Cfe.Language.Construct.Union over
open import Cfe.Language.Indexed.Construct.Iterate over
open import Data.Fin as F hiding (_ā¤_; cast)
open import Data.Nat as ā hiding (_ā¤_; _ā_)
open import Data.Product
open import Data.Vec
open import Level renaming (suc to lsuc) hiding (Lift)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

infix 10 _[_/_]
infix 7 _ā_
infix 6 _āØ_
infix 4 _ā_

data Expression : ā ā Set c where
  ā„ : ā {n} ā Expression n
  Īµ : ā {n} ā Expression n
  Char : ā {n} ā C ā Expression n
  _āØ_ : ā {n} ā Expression n ā Expression n ā Expression n
  _ā_ : ā {n} ā Expression n ā Expression n ā Expression n
  Var : ā {n} ā Fin n ā Expression n
  Ī¼ : ā {n} ā Expression (suc n) ā Expression n

cast : ā {m n} ā .(_ : m ā” n) ā Expression m ā Expression n
cast eq ā„ = ā„
cast eq Īµ = Īµ
cast eq (Char x) = Char x
cast eq (eā āØ eā) = cast eq eā āØ cast eq eā
cast eq (eā ā eā) = cast eq eā ā cast eq eā
cast eq (Var i) = Var (F.cast eq i)
cast eq (Ī¼ e) = Ī¼ (cast (cong suc eq) e)

wkn : ā {n} ā Expression n ā Fin (suc n) ā Expression (suc n)
wkn ā„ i = ā„
wkn Īµ i = Īµ
wkn (Char x) i = Char x
wkn (eā āØ eā) i = wkn eā i āØ wkn eā i
wkn (eā ā eā) i = wkn eā i ā wkn eā i
wkn (Var x) i = Var (punchIn i x)
wkn (Ī¼ e) i = Ī¼ (wkn e (suc i))

_[_/_] : ā {n} ā Expression (suc n) ā Expression n ā Fin (suc n) ā Expression n
ā„ [ eā² / i ] = ā„
Īµ [ eā² / i ] = Īµ
Char x [ eā² / i ] = Char x
(eā āØ eā) [ eā² / i ] = eā [ eā² / i ] āØ eā [ eā² / i ]
(eā ā eā) [ eā² / i ] = eā [ eā² / i ] ā eā [ eā² / i ]
Var j [ eā² / i ] with i F.ā j
... | yes iā”j = eā²
... | no iā¢j = Var (punchOut iā¢j)
Ī¼ e [ eā² / i ] = Ī¼ (e [ wkn eā² F.zero / suc i ])

rotate : ā {n} ā Expression n ā (i j : Fin n) ā .(_ : i F.ā¤ j) ā Expression n
rotate ā„ _ _ _ = ā„
rotate Īµ _ _ _ = Īµ
rotate (Char x) _ _ _ = Char x
rotate (eā āØ eā) i j iā¤j = rotate eā i j iā¤j āØ rotate eā i j iā¤j
rotate (eā ā eā) i j iā¤j = rotate eā i j iā¤j ā rotate eā i j iā¤j
rotate {suc n} (Var k) i j _ with i F.ā k
... | yes iā”k = Var j
... | no iā¢k = Var (punchIn j (punchOut iā¢k))
rotate (Ī¼ e) i j iā¤j = Ī¼ (rotate e (suc i) (suc j) (sā¤s iā¤j))

ā¦_ā§ : ā {n : ā} ā Expression n ā Vec (Language (c ā ā)) n ā Language (c ā ā)
ā¦ ā„ ā§ _ = Lift (c ā ā) ā
ā¦ Īµ ā§ _ = Lift ā ļ½Īµļ½
ā¦ Char x ā§ _ = Lift ā ļ½ x ļ½
ā¦ eā āØ eā ā§ Ī³ = ā¦ eā ā§ Ī³ āŖ ā¦ eā ā§ Ī³
ā¦ eā ā eā ā§ Ī³ = ā¦ eā ā§ Ī³ āā ā¦ eā ā§ Ī³
ā¦ Var n ā§ Ī³ = lookup Ī³ n
ā¦ Ī¼ e ā§ Ī³ = ā (Ī» X ā ā¦ e ā§ (X ā· Ī³))

_ā_ : {n : ā} ā Expression n ā Expression n ā Set (lsuc (c ā ā))
eā ā eā = ā Ī³ ā ā¦ eā ā§ Ī³ š.ā ā¦ eā ā§ Ī³

rank : {n : ā} ā Expression n ā ā
rank ā„ = 0
rank Īµ = 0
rank (Char _) = 0
rank (eā āØ eā) = suc (rank eā ā.+ rank eā)
rank (eā ā _) = suc (rank eā)
rank (Var _) = 0
rank (Ī¼ e) = suc (rank e)

infix 4 _<įµ£āāā_

_<įµ£āāā_ : ā {m n} ā REL (Expression m) (Expression n) _
e <įµ£āāā eā² = rank e ā.< rank eā²
