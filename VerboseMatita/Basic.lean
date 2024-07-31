import Lean -- To allow Ctrl+Click over Lean syntax
import Verbose.English.All

open Lean
open Lean.Elab.Tactic

namespace matita

-- Bugs:
--  assume/suppose/we choose/we split the proof: enforce that the type is a product and that is has the right sort
--  "it suffices to prove"/"such that"/"we choose" (because of Verbose)
--  by ... not very strong
--  case is bugged
--  and/exist elim: enforce that the type is the expected one
--  solve_by_elim only L  is weak (does not add new hypotheses to L)

-- Todo:
--  should we proceed by cases be used only for ∨_e and be changed to
--   matitaJust we proceed by cases
--   to avoid confusion with we proceed by induction?
--  is suffices to prove: implement using matitaJust
--  eliminazione dell'assurdo: done works good? add other syntax like "absurdum"? try to remove it from
--     solve_by_elim? (possibly impossible?)
--  suppose ... that is equivalent to
--  case tactics that makes the hypothesis explicit
--  letin
--  that is equivalent to after by just we proved, that is equivalent to, we claim, it suffices to prove e le premesse introdotte da and_e
--  by induction hypothesis we know
--  conclude/obtain/=

-- Ugly:
--  code duplication for empty matitaJust ; may use obviously? or a _empty_ thing?
--  code duplication for omitting name of hypothesis in "we proved"
--  code duplication for using Or.inl, Or.inr automatically in solve_by_elim

-- Implemented:
--  assume [that is equivalent to]
--  suppose [that is equivalent to]
--  done
--  we proved
--  we need to prove [that is equivalent to]
--  we claim ... as ... by ...
--  we proceed by cases on
--  we proceed by induction on
--  case
--  by it suffice to prove
--  we split the proof
--  we choose .. and prove .. [that is equivalent to]
--  we proved .. and ..
--  let .. such that

-- Debugging:
--  logInfo          chiamata
--  trace            tattica
--  Lean.addRawTrace

-- Tactics example:
-- elab_rules : tactic
-- |`(tactic| then) =>
--   withMainContext do
--    let x := (← getMainDecl).lctx.lastDecl.map (fun x ↦ x.toExpr)
--    Lean.addRawTrace x -/

syntax "_last_hypothesis_" : term

elab_rules : term
 |`(term| _last_hypothesis_) => do (← Lean.getLCtx).lastDecl.map (fun x ↦ x.toExpr) -- bug here exclude recursive call to theorem

declare_syntax_cat matitaEquivalent

syntax "that " "is " "equivalent " "to " term : matitaEquivalent

syntax "assume " ident " : " term (matitaEquivalent)? : tactic

macro_rules
  | `(tactic| assume $ident : $type) => `(tactic| intro $ident:ident <;> guard_hyp _last_hypothesis_ :ₛ $type)
  | `(tactic| assume $ident : $type that is equivalent to $type₂) =>
    `(tactic| assume $ident : $type <;> change $type₂ at _last_hypothesis_)


syntax "suppose " term (matitaEquivalent)? (" as " ident)? : tactic

macro_rules
  | `(tactic| suppose $term as $ident) => `(tactic| intro $ident:ident <;> guard_hyp _last_hypothesis_ :ₛ $term)
  | `(tactic| suppose $term) => `(tactic| intro <;> guard_hyp _last_hypothesis_ :ₛ $term)
  | `(tactic| suppose $term that is equivalent to $type $[as $ident]? ) =>
    `(tactic| suppose $term $[as $ident]? <;> change $type at _last_hypothesis_)


-- one more bug here
--macro_rules
--  | `(matitaJust | by ) =>
--    `(Lean.Parser.Tactic.SolveByElim.arg | [])

theorem iff_e: ∀A B: Prop, (A ↔ B) → (A → B) ∧ (B → A) := by
 intros A B U ; cases U ; constructor <;> solve_by_elim

declare_syntax_cat matitaJust

syntax "thus "? ("by " ident,+)? : matitaJust

-- simplify the code now that after by the list must be non empty?
-- factorize Or.inr/Or.inl
def matitaJust_to_solveByElimArg : TSyntax `matitaJust -> MacroM (TSyntax ``Lean.Parser.Tactic.SolveByElim.args)
  | `(matitaJust | thus by $[$terms],* ) => do
    let args ← terms.mapM fun x => `(Lean.Parser.Tactic.SolveByElim.arg| $x:ident)
    `(Lean.Parser.Tactic.SolveByElim.args| [$(args.push (← `(Lean.Parser.Tactic.SolveByElim.arg| _last_hypothesis_))),*, Or.inr, Or.inl, matita.iff_e])
  | `(matitaJust | by $[$terms],* ) =>
    `(Lean.Parser.Tactic.SolveByElim.args| [$[$terms:ident],*, Or.inr, Or.inl, matita.iff_e])
  | `(matitaJust | thus ) =>
    `(Lean.Parser.Tactic.SolveByElim.args| [_last_hypothesis_, Or.inr, Or.inl, matita.iff_e])
--  | `(matitaJust | ) =>
--    `(Lean.Parser.Tactic.SolveByElim.args| [])
  | _ => -- panic! "xxx" -- thereis  the right throwXXX
    `(Lean.Parser.Tactic.SolveByElim.args| [Or.inr, Or.inl, matita.iff_e])

syntax matitaJust " done" : tactic

macro_rules
  | `(tactic | $mj:matitaJust done) => do
    `(tactic | solve_by_elim only $(← matitaJust_to_solveByElimArg mj))
  | `(tactic | done) => do
    `(tactic | solve_by_elim only [Or.inr, Or.inl, matita.iff_e])

syntax (matitaJust)? "we " " proved " term ("as " ident)? : tactic
syntax (matitaJust)? "we " " proved " term "as " ident "and " term "as " ident : tactic
syntax (matitaJust)? "let " ident ": " term "such that " term "as " ident : tactic

-- duplicated code, not nice
-- idea: factorize a bit using a _empty_matita_just ?  or just use obviously?
macro_rules
  | `(tactic | $mj:matitaJust we proved $term as $ident) => do
    let x ← matitaJust_to_solveByElimArg mj
    `(tactic | have $ident : $term := by solve_by_elim only $x)
  | `(tactic | $mj:matitaJust we proved $term) => do
    let x ← matitaJust_to_solveByElimArg mj
    `(tactic | have _ : $term := by solve_by_elim only $x)
  | `(tactic | we proved $term as $ident) =>
    `(tactic | have $ident : $term := by solve_by_elim only [Or.inr, Or.inl, matita.iff_e])
  | `(tactic | we proved $term) =>
    `(tactic | have _ : $term := by solve_by_elim only [Or.inr, Or.inl, matita.iff_e])
  | `(tactic | $mj:matitaJust we proved $term₁ as $ident₁ and $term₂ as $ident₂) =>
    `(tactic | $mj:matitaJust we proved $term₁ ∧ $term₂ <;> cases _last_hypothesis_ <;> case _ $ident₁:ident $ident₂:ident)
  | `(tactic | we proved $term₁ as $ident₁ and $term₂ as $ident₂) =>
    `(tactic | we proved $term₁ ∧ $term₂ <;> cases _last_hypothesis_ <;> case _ $ident₁:ident $ident₂:ident)
  | `(tactic | $mj:matitaJust let $ident₁ : $term₁ such that $term₂ as $ident₂) =>
    `(tactic | $mj:matitaJust we proved ∃$ident₁:ident : $term₁, $term₂ <;> cases _last_hypothesis_ <;> case _ $ident₁:ident $ident₂:ident)
  | `(tactic | let $ident₁ : $term₁ such that $term₂ as $ident₂) =>
    `(tactic | we proved ∃$ident₁:ident : $term₁, $term₂ <;> cases _last_hypothesis_ <;> case _ $ident₁:ident $ident₂:ident)

syntax "we " "need " "to " "prove " term (matitaEquivalent)? : tactic

macro_rules
 | `(tactic | we need to prove $term) =>
  `(tactic | guard_target =ₛ $term)
 | `(tactic | we need to prove $exp that is equivalent to $inf) =>
  `(tactic | we need to prove $exp <;> change $inf)

macro "we " "split " "the " "proof " : tactic => `(tactic| first | apply And.intro | apply Iff.intro)

macro "we " "claim " stmt:term "as " name:ident "by" colGt prf:tacticSeq : tactic => `(tactic|have $name : $stmt := by $prf)
macro "we " "claim " stmt:term                  "by" colGt prf:tacticSeq : tactic => `(tactic|have _ : $stmt := by $prf)

macro "we " "proceed " "by " "cases " "on " name:ident "to " "prove " stmt:term : tactic => `(tactic|guard_target =ₛ $stmt <;> cases $name:term)

macro "we " "proceed " "by " "induction " "on " name:ident ": " type:term "to " "prove " stmt:term : tactic => `(tactic|guard_target =ₛ ∀$name : $type, $stmt <;> intro $name:ident <;> induction $name:term)

syntax "by " term "it suffices to prove " term : tactic -- "it suffices to prove " is a keyword in Verbose

elab_rules : tactic
 | `(tactic| by $term:term it suffices to prove $arg) => bySufficesTac term #[arg]

syntax "we choose " term "and " "prove " term (matitaEquivalent)? : tactic

macro_rules
 | `(tactic| we choose $term₁ and prove $term₂) => `(tactic| existsi $term₁ <;> we need to prove $term₂)
 | `(tactic| we choose $term₁ and prove $term₂ that is equivalent to $term₃) =>
   `(tactic| we choose $term₁ and prove $term₂ <;> change $term₃)

end matita

namespace set_theory

/- set, ∈ -/
axiom set: Type
axiom mem: set → set → Prop

infix:50 (priority := high) " ∈ " => mem

-- Extensionality
axiom ax_extensionality: ∀A B, (∀Z, Z ∈ A ↔ Z ∈ B) → A = B

-- Inclusion
def incl (A:set) (B:set) : Prop :=
 ∀Z, Z ∈ A → Z ∈ B

infix:50 (priority := high) " ⊆ " => incl

-- Emptyset  ∅
axiom emptyset: set
notation:max "∅" => emptyset
axiom ax_empty: ∀X, (X ∈ ∅)→ False

-- Intersection ∩
axiom intersect: set → set → set
infix:80 (priority := high) " ∩ " => intersect
axiom ax_intersect1: ∀A B, ∀Z, (Z ∈ A ∩ B → Z ∈ A ∧ Z ∈ B)
axiom ax_intersect2: ∀A B, ∀Z, (Z ∈ A ∧ Z ∈ B → Z ∈ A ∩ B)

-- Union ∪
axiom union: set → set → set
infix:70 (priority := high) " ∪ " => union
axiom ax_union1: ∀A B, ∀Z, (Z ∈ A ∪ B → Z ∈ A ∨ Z ∈ B)
axiom ax_union2: ∀A B, ∀Z, (Z ∈ A ∨ Z ∈ B → Z ∈ A ∪ B)

-- Proofs in matita
namespace matita

theorem reflexivity_inclusion: ∀A, A ⊆ A := by
 assume A: set
 we need to prove A ⊆ A that is equivalent to ∀Z, Z ∈ A → Z ∈ A
 assume Z: set
 suppose Z ∈ A
 thus done

theorem transitivity_inclusion: ∀A B C, A ⊆ B → B ⊆ C → A ⊆ C := by
 assume A: set
 assume B: set
 assume C: set
 suppose A ⊆ B that is equivalent to ∀Z, Z ∈ A → Z ∈ B as H₁
 suppose B ⊆ C that is equivalent to ∀Z, Z ∈ B → Z ∈ C as H₂
 we need to prove A ⊆ C that is equivalent to ∀Z, Z ∈ A → Z ∈ C
 assume Z: set
 suppose Z ∈ A
 thus by H₁ we proved Z ∈ B
 thus by H₂ done

theorem empty_absurd: ∀X A, X ∈ ∅ → X ∈ A := by
 assume X : set
 assume A : set
 suppose X ∈ ∅
 thus by ax_empty done

theorem intersection_idempotent: ∀A, A ∩ A = A := by
 assume A : set
 by ax_extensionality it suffices to prove ∀Z, Z ∈ A ∩ A ↔ Z ∈ A
 assume Z : set
 we split the proof
 . we need to prove Z ∈ A ∩ A → Z ∈ A
   suppose Z ∈ A ∩ A
   thus by ax_intersect1 we proved Z ∈ A as H₁ and Z ∈ A as H₂
   thus done
 . we need to prove Z ∈ A → Z ∈ A ∩ A
   suppose Z ∈ A
   thus by ax_intersect2 done

theorem union_symmetric: ∀A B, A ∪ B = B ∪ A := by
 assume A : set
 assume B : set
 by ax_extensionality it suffices to prove ∀Z, Z ∈ A ∪ B ↔ Z ∈ B ∪ A
 assume Z : set
 we split the proof
 . we need to prove Z ∈ A ∪ B → Z ∈ B ∪ A
   suppose Z ∈ A ∪ B
   thus by ax_union1 we proved Z ∈ A ∨ Z ∈ B as H
   we proceed by cases on H to prove Z ∈ B ∪ A
   . case a.mp.inl H
     thus we proved Z ∈ B ∨ Z ∈ A  -- you can skip this step
     thus by ax_union2 done
   . case a.mp.inr H
     thus by ax_union2 done
 . we need to prove Z ∈ B ∪ A → Z ∈ A ∪ B
   suppose Z ∈ B ∪ A
   thus by ax_union1 we proved Z ∈ B ∨ Z ∈ A as H
   we proceed by cases on H to prove Z ∈ A ∪ B
   . case a.mpr.inl H
     thus by ax_union2 done
   . case a.mpr.inr H
     thus by ax_union2 done

theorem exists_example: (∃A, A ∈ ∅) → ∀A, A ∈ A := by
 suppose ∃A, A ∈ ∅
 thus let A : set such that A ∈ ∅ as H
 thus by ax_empty we proved False
 thus done -- absurd elimination used here

 theorem exists_example2: ∀A, ∃B, B ⊆ A := by
  assume A: set
  we choose ∅ and prove ∅ ⊆ A that is equivalent to ∀Z, Z ∈ ∅ → Z ∈ A
  assume Z: set
  suppose Z ∈ ∅
  thus by ax_empty done

theorem iff_example: ∀A B: Prop, ((A → B) ∧ (B → A)) → True := by
 assume A: Prop
 assume B: Prop
 suppose (A → B) ∧ (B → A)
 thus we proved A → B as H₁ and B → A as H₂
 done

theorem iff_example2: ∀A B: Prop, (A ↔ B) → (B ↔ A) := by
 assume A: Prop
 assume B: Prop
 suppose A ↔ B
 thus we proved A → B as H₁ and B → A as H₂
 we split the proof
 . we need to prove B → A
   by H₂ done
 . we need to prove A → B
   by H₁ done

-- theorem intersect_empty: ∀A. A ∩ ∅ = ∅.
-- theorem antisymmetry_inclusion: ∀A,B. A ⊆ B → B ⊆ A → A = B.
-- theorem intersect_commutative: ∀A,B. A ∩ B = B ∩ A.

def append: List α → List α → List α
| [], l₂ => l₂
| (x::l₁), l₂ => x::(append l₁ l₂)

theorem append_empty: ∀l: List ℕ, append l [] = l := by
 we proceed by induction on l: List ℕ to prove append l [] = l
 . case nil
   we need to prove append ([] : List ℕ) [] = [] that is equivalent to [] = []
   done
 . case cons y l' II
   we need to prove append (y::l') [] = y::l' that is equivalent to y::(append l' []) = y::l'
   -- by II, congrFun, congrArg done  -- it works
   calc
        y::(append l' [])
    _ = y::l'              := by rw [II]

def sumL: List ℕ → ℕ
| [] => 0
| x::l => x + sumL l

inductive Tree (α : Type u) where
| Leaf : α → Tree α
| Node : Tree α → Tree α → Tree α

open Tree

def collect: Tree α → List α
| Leaf n => n::[]
| Node T1 T2 => append (collect T1) (collect T2)

def sumT: Tree ℕ → ℕ
| Leaf n => n
| Node T1 T2 => sumT T1 + sumT T2

theorem sumL_append: ∀l₁ l₂, sumL (append l₁ l₂) = sumL l₁ + sumL l₂ := by
 we proceed by induction on l₁:List ℕ to prove ∀l₂, sumL (append l₁ l₂) = sumL l₁ + sumL l₂
 . case nil
   we need to prove ∀l₂, sumL (append [] l₂) = sumL [] + sumL l₂
    that is equivalent to ∀l₂, sumL l₂ = 0 + sumL l₂
   --assume l₂: List ℕ
   -- calc
   --     sumL l₂
   -- _ = 0 + sumL l₂ := by simp only [zero_add]
   by zero_add, Eq.symm done
 . case cons x l II
   we need to prove ∀l₂, sumL (append (x::l) l₂) = sumL (x::l) + sumL l₂
    that is equivalent to ∀l₂, x + sumL (append l l₂) = x + sumL l + sumL l₂
   -- simp [II, congrFun, congrArg, Nat.add_assoc]
   -- by II, congrFun, congrArg, Nat.add_assoc done
   assume l₂: List ℕ
   calc
        x + sumL (append l l₂)
    _ = x + (sumL l + sumL l₂)    := by rw [II]
    _ = x + sumL l + sumL l₂      := by rw [Nat.add_assoc]

theorem sumL_collect: ∀T, sumL (collect T) = sumT T := by
 we proceed by induction on T:Tree ℕ to prove sumL (collect T) = sumT T
 . case Leaf n
   we need to prove sumL (collect (Leaf n)) = sumT (Leaf n)
    that is equivalent to n = n
   done
 . case Node T₁ T₂ II₁ II₂
   we need to prove sumL (collect (Node T₁ T₂)) = sumT (Node T₁ T₂)
    that is equivalent to sumL (append (collect T₁) (collect T₂)) = sumT T₁ + sumT T₂
   -- simp [sumL_append, II₁, II₂]
   calc
       sumL (append (collect T₁) (collect T₂))
   _ = sumL (collect T₁) + sumL (collect T₂)   := by rw [sumL_append]
   _ = sumT T₁ + sumT T₂                       := by rw [II₁, II₂]

end matita

section verbose
-- Proofs in Lean/verbose-lean

-- procedural proof
theorem reflexivity_inclusion: ∀A, A ⊆ A := by
 intro A
 whnf
 intro Z
 intro H
 apply H

-- declarative proof, explicit hypotheses
theorem reflexivity_inclusion2: ∀A, A ⊆ A := by
 Fix A -- or Fix A : set
 whnf -- ??
 Fix Z
 Assume HA : Z ∈ A
 We conclude by HA

-- declarative proof, implicit hypotheses
theorem reflexivity_inclusion3: ∀A, A ⊆ A := by
 Fix A -- or Fix A : set
 whnf -- ??
 Fix Z
 Assume HA : Z ∈ A
 Since Z ∈ A we conclude that Z ∈ A

theorem empty_absurd: ∀X A, X ∈ ∅ → X ∈ A := by
 Fix X A
 Assume H: X ∈ ∅
 By ax_empty applied to X using H we get K: False
 Let's prove it's contradictory
 We conclude by K

end verbose
