import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.LocatedCompactUp.TasteGate

namespace BEDC.Derived.LocatedCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedCompactCarrier [AskSetup] [PackageSetup]
    (X L F A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist BMark
  UnaryHistory X ∧ UnaryHistory L ∧ UnaryHistory F ∧ UnaryHistory A ∧ Cont L F C ∧
    hsame H (append X A) ∧ PkgSig bundle P pkg ∧ hsame N (append C P)

theorem LocatedCompactCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X L F A H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCompactCarrier X L F A H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist => LocatedCompactCarrier X L F A H C P N bundle pkg /\ hsame row N)
        (fun row : BHist => LocatedCompactCarrier X L F A H C P N bundle pkg /\ hsame row N)
        (fun row : BHist => LocatedCompactCarrier X L F A H C P N bundle pkg /\ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist BMark
  intro carrier
  constructor
  · constructor
    · exact Exists.intro N (And.intro carrier (hsame_refl N))
    · intro row _source
      exact hsame_refl row
    · intro row row' same
      exact hsame_symm same
    · intro row row' row'' sameRow sameRow'
      exact hsame_trans sameRow sameRow'
    · intro row row' sameRows sourceRow
      exact And.intro carrier (hsame_trans (hsame_symm sameRows) sourceRow.right)
  · intro _row source
    exact source
  · intro _row source
    exact source

theorem LocatedCompactCarrier_totally_bounded_handoff [AskSetup] [PackageSetup]
    {X L F A H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCompactCarrier X L F A H C P N bundle pkg ->
      UnaryHistory L ∧ UnaryHistory F ∧ UnaryHistory A ∧ UnaryHistory C ∧ Cont L F C ∧
        hsame H (append X A) ∧ PkgSig bundle P pkg ∧ hsame N (append C P) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame
  intro carrier
  have cUnary : UnaryHistory C :=
    unary_cont_closed carrier.right.left carrier.right.right.left
      carrier.right.right.right.right.left
  exact
    And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro cUnary
            (And.intro carrier.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.left
                (And.intro carrier.right.right.right.right.right.right.left
                  carrier.right.right.right.right.right.right.right))))))

theorem LocatedCompactCarrier_public_export_surface [AskSetup] [PackageSetup]
    {X L F A H C P N publicRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCompactCarrier X L F A H C P N bundle pkg ->
      Cont F L publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row L ∨ hsame row F ∨ hsame row A ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row publicRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont L F C ∧ Cont F L publicRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
            hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier publicRoute publicPkg
  obtain ⟨_xUnary, lUnary, fUnary, _aUnary, carrierCont, _transportRow,
    provenancePkg, _nameRow⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed fUnary lUnary publicRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row L ∨ hsame row F ∨ hsame row A ∨ hsame row H ∨
            hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row publicRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont L F C ∧ Cont F L publicRead ∧
            PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (And.intro (hsame_refl publicRead) publicUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact
          And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left)
            (unary_transport sourceRow.right sameRows)
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        And.intro sourceRow.right
          (And.intro carrierCont
            (And.intro publicRoute (And.intro provenancePkg publicPkg)))
  }
  exact And.intro cert publicUnary

end BEDC.Derived.LocatedCompactUp
