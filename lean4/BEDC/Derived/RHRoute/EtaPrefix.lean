import BEDC.Derived.RHRoute.ConstructiveZeta

/-!
Discharged facts about the finite eta prefix.

These are deliberately modest, but they are *discharged* — proved over the
`etaTermList` / `etaPartialSum` definitions of `ConstructiveZeta`, not assumed
via a witness field. They are the first non-hollow entries for an RHRoute
hard-content ledger: their proofs compute over the definitions rather than
projecting a structure field, concluding `True`, or relying on a rigged
representation. The genuine analytic tail bound remains a separate obligation
that first requires the evaluator definitions to expose a kernel-indexed bound.

The proofs avoid the Lean core `List.length_map` / `List.length_range` lemmas
because those carry a `propext` dependency, which the project's
`axiom-purity --strict` gate forbids; the length facts are re-derived here from
first principles so the discharge stays Classical.choice / Quot.sound / propext
free.
-/

namespace BEDC.Derived.RHRoute.EtaPrefix

open BEDC.Derived.RHRoute.ConstructiveZeta

/-- `List.map` preserves length. Structural, propext-free. -/
private theorem map_length {α β : Type _} (f : α → β) :
    ∀ l : List α, (List.map f l).length = l.length
  | [] => rfl
  | _ :: t => congrArg (· + 1) (map_length f t)

/-- Length of the `range.loop` accumulator recursion, propext-free. -/
private theorem range_loop_length :
    ∀ (n : Nat) (acc : List Nat),
      (List.range.loop n acc).length = n + acc.length
  | 0, acc => (Nat.zero_add acc.length).symm
  | n + 1, acc =>
      ((range_loop_length n (n :: acc)).trans
        (Nat.add_succ n acc.length)).trans
        (Nat.succ_add n acc.length).symm

/-- `(List.range n).length = n`, propext-free. -/
private theorem range_length (n : Nat) : (List.range n).length = n :=
  (range_loop_length n []).trans (Nat.add_zero n)

/-- The finite eta prefix produced by the evaluator has exactly `N` terms.
Discharged from the `etaTermList = List.map … (List.range N)` definition, not
assumed via a witness field. -/
-- @hard_discharge: eta-finite-prefix-length
theorem etaTermList_length {s : RationalStripPoint}
    (kernel : LocatedExpLogKernel s) (N precision : Nat) :
    (etaTermList kernel N precision).length = N := by
  unfold etaTermList
  rw [map_length, range_length]

/-- The empty eta prefix sums to the zero rational-complex value. -/
theorem etaPartialSum_zero {s : RationalStripPoint}
    (kernel : LocatedExpLogKernel s) (precision : Nat) :
    etaPartialSum kernel 0 precision = ratComplexZero := by
  rfl

end BEDC.Derived.RHRoute.EtaPrefix
