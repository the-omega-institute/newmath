import BEDC.Derived.ClosedBoundedIntervalUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedBoundedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_real_seal_nonescape [AskSetup] [PackageSetup]
    {L U O Q D S R E H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L -> UnaryHistory U -> UnaryHistory O -> UnaryHistory Q ->
      UnaryHistory D -> UnaryHistory S -> UnaryHistory R -> UnaryHistory E ->
        Cont L U O ->
          Cont Q D S ->
            Cont S R E ->
              PkgSig bundle P pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row E ∧ UnaryHistory row)
                    (fun _row : BHist => Cont L U O ∧ Cont Q D S ∧ Cont S R E)
                    (fun row : BHist => PkgSig bundle P pkg ∧ hsame row E)
                    hsame ∧
                  UnaryHistory E ∧ Cont L U O ∧ Cont Q D S ∧ Cont S R E := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _lUnary _uUnary _oUnary _qUnary _dUnary _sUnary _rUnary eUnary endpointRoute
    streamRoute sealRoute pkgRow
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row E ∧ UnaryHistory row)
          (fun _row : BHist => Cont L U O ∧ Cont Q D S ∧ Cont S R E)
          (fun row : BHist => PkgSig bundle P pkg ∧ hsame row E)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro E ⟨hsame_refl E, eUnary⟩
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact ⟨endpointRoute, streamRoute, sealRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨pkgRow, source.left⟩
  }
  exact ⟨cert, eUnary, endpointRoute, streamRoute, sealRoute⟩

end BEDC.Derived.ClosedBoundedIntervalUp
