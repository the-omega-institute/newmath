import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompleteMetricLimitUniquenessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompleteMetricLimitUniquenessCarrier [AskSetup] [PackageSetup]
    (A L0 L1 M Z S H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory A ∧ UnaryHistory L0 ∧ UnaryHistory L1 ∧ UnaryHistory M ∧
    UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CompleteMetricLimitUniquenessCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {A L0 L1 M Z S H C P N zeroRead separatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompleteMetricLimitUniquenessCarrier A L0 L1 M Z S H C P N bundle pkg →
      Cont M Z zeroRead →
        Cont zeroRead S separatedRead →
          PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row A ∨ hsame row L0 ∨ hsame row L1 ∨ hsame row M ∨
                    hsame row Z ∨ hsame row S ∨ hsame row separatedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont M Z zeroRead ∧
                    Cont zeroRead S separatedRead ∧ PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory zeroRead ∧ UnaryHistory separatedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier zeroRoute separatedRoute namePkg
  rcases carrier with
    ⟨_AUnary, _L0Unary, _L1Unary, MUnary, ZUnary, SUnary, _HUnary, _CUnary,
      _PUnary, _NUnary, _provenancePkg, _namePkgFromCarrier⟩
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed MUnary ZUnary zeroRoute
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed zeroReadUnary SUnary separatedRoute
  have sourceSeparated :
      (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row) separatedRead :=
    And.intro (hsame_refl separatedRead) separatedReadUnary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row A ∨ hsame row L0 ∨ hsame row L1 ∨ hsame row M ∨ hsame row Z ∨
            hsame row S ∨ hsame row separatedRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont M Z zeroRead ∧ Cont zeroRead S separatedRead ∧
            PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro separatedRead sourceSeparated
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
          And.intro
            (hsame_trans (hsame_symm sameRows) sourceRow.left)
            (unary_transport sourceRow.right sameRows)
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.right
        (And.intro zeroRoute (And.intro separatedRoute namePkg))
  }
  exact And.intro cert (And.intro zeroReadUnary separatedReadUnary)

end BEDC.Derived.CompleteMetricLimitUniquenessUp
