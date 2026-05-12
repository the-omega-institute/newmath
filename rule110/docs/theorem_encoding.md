# Theorem encoding: 4 msame lemmas

Each of the 4 msame theorems from `lean4/BEDC/FKernel/Mark.lean` is encoded
in 2 manifest files: an `enum` version (manual case enumeration) and an
`algo` version (cyclic-tag-program-as-decision-procedure template).

## msame_refl : ∀ m, msame m m

- 2 cases: m=b0 (input="011011"), m=b1 (input="10111011")
- Both inputs decode to two equal BMark events
- `enum`: documentary; runtime check via decoder.
- `algo`: pragmatic identity recognizer (vacuous productions); same runtime check.

## msame_symm : msame m n → msame n m

- 4 cases over (m, n) ∈ BMark²
- Cases (b0,b0) and (b1,b1): trivial reflexive
- Cases (b0,b1) and (b1,b0): vacuous (antecedent false)
- Verification: decoder + bit equality / inequality check

## msame_trans : msame a b → msame b c → msame a c

- 8 cases over (a, b, c) ∈ BMark³
- 2 trivial cases (a=b=c): (b0,b0,b0), (b1,b1,b1)
- 6 vacuous cases (at least one antecedent false)
- Verification: decode three events, verify transitivity holds in trivial cases,
  ignore vacuous

## msame_no_confusion : (msame b0 b1 → False) ∧ (msame b1 b0 → False)

- 2 cases: (b0,b1) and (b1,b0)
- Both require decoded events to be unequal (which they are by BMark constructor distinctness)
- Verification: decoder + bit inequality check

## Why enum + algo for BMark?

BMark is a finite 2-element domain — all msame theorems are trivially
decidable by enumeration. The `algo` version exists as a **template for
milestone-3 (BHist)** where the domain is countably infinite and true
algorithm-as-recognizer becomes necessary.

For BMark, `enum` and `algo` semantically collapse; productions in `algo`
are vacuous (size-1 zero-bit production for divide-by-zero safety in the CT
evaluator), and verification logic is identical to enum. This is a
deliberate choice: shipping both forms now keeps the design pattern visible
for milestone-3 without inventing artificial CT programs for finite cases.
