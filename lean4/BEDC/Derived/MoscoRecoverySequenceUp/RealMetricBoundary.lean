import BEDC.Derived.MoscoRecoverySequenceUp.NameCertObligations

namespace BEDC.Derived.MoscoRecoverySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MoscoRecoverySequenceCarrier [AskSetup] [PackageSetup]
    (X F W A G Q E M H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory X ∧ UnaryHistory F ∧ UnaryHistory W ∧ UnaryHistory A ∧
    UnaryHistory G ∧ UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory M ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem MoscoRecoverySequenceRealMetricBoundary [AskSetup] [PackageSetup]
    {X F W A G Q E M H C P N recoveryRead valueRead sealRead metricRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MoscoRecoverySequenceCarrier X F W A G Q E M H C P N bundle pkg →
      Cont A G recoveryRead →
        Cont recoveryRead Q valueRead →
          Cont valueRead E sealRead →
            Cont sealRead M metricRead →
              Cont metricRead N namedRead →
                hsame H C →
                  SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row G ∨ hsame row Q ∨ hsame row E ∨
                        hsame row M ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont A G recoveryRead ∧
                        Cont recoveryRead Q valueRead ∧ Cont valueRead E sealRead ∧
                          Cont sealRead M metricRead ∧ Cont metricRead N namedRead ∧
                            hsame H C)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier recoveryRoute valueRoute sealRoute metricRoute namedRoute transportLock
  obtain ⟨_xUnary, _fUnary, _wUnary, aUnary, gUnary, qUnary, eUnary, mUnary,
    _hUnary, _cUnary, _pUnary, nUnary, _pPkg, _nPkg⟩ := carrier
  have recoveryUnary : UnaryHistory recoveryRead :=
    unary_cont_closed aUnary gUnary recoveryRoute
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed recoveryUnary qUnary valueRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed valueUnary eUnary sealRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed sealUnary mUnary metricRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed metricUnary nUnary namedRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, recoveryRoute, valueRoute, sealRoute, metricRoute, namedRoute,
          transportLock⟩
  }

end BEDC.Derived.MoscoRecoverySequenceUp
