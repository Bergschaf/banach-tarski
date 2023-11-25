import Mathlib.Data.Real.Basic

structure Group1 (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one
  mul_right_inv : ∀ x : α, mul x (inv x) = one

structure Subgroup₁  (α : Type*) [Group α] where
  carrier : Set α
  is_subgroup : this ⊂ carrier

structure Letters (α: Type*) where
  word : Type
  letter : Type
  is_type : ∀ x : letter, ∃ y : word, x ≡ y

  A : letter
  B : letter

  mul : word → word → word
  one : letter
  inv : letter → letter
  mul_one : ∀ x : word, mul x one = x
  one_mul : ∀ x : word, mul one x = x
  mul_left_inv : ∀ x : letter, mul (inv x) x = one
  mul_right_inv : ∀ x : letter, mul x (inv x) = one
  only_letter : ∀ x : letter, x ∈ [A,B, inv A, inv B, one]

  ---word : List this
  --nul : List one
  --mul_letter_word : mul this (List this) -> mul (mul this this) (List this)
  --mul_word_letter : mul (List this) this -> mul (List this) (mul this this)
  --mul_word_word : mul (List this) (List this) -> mul (mul (List this) this) (List this)

  --cancel : List this -> List this




structure Word (α : Type*) where
  carrier : Set α
  subset : Set α
  is_subset : subset ⊂ carrier
  word: 
  word_insert: subset.Elem -> List subset.Elem ->  List subset.Elem



#check Word.word


structure FreeGroup₁ (α : Type*) where
  carrier : Set α

  words : Set (Word α)


  is_subgroup : this ⊂ carrier
  h : ∀ z, z ∈ carrier
