/-!
This module declares the `All` typeclass, which classifies a type as being
finite and enumerable (i.e. not too large).
-/


/--
Types that are finite and enumerable.
-/
class All (α) where
  all : Array α
  mem_all : ∀ x, x ∈ all


abbrev all {α} [All α] : Array α := All.all
abbrev allOf (α : Type) [All α] : Array α := All.all
abbrev mem_all {α} [All α] : ∀ x, x ∈ allOf α := All.mem_all


/-- Easier way to define `All` instances sometimes. -/
def All.mk'
  {α : Type}
  (all : Array α)
  (mem_all : (∀ x, x ∈ all) := by intro h ; cases h <;> decide)
  : All α :=
  { all := all, mem_all := mem_all }


instance [All α] {p : α -> Prop} [DecidablePred p]
: Decidable (∀ r : α, p r) :=
  have a : Decidable (∀ r ∈ all, p r) := inferInstance
  match a with
  | isTrue h => isTrue (fun r => h r (mem_all _))
  | isFalse h => isFalse (fun h' => h (fun r _ => h' r))


