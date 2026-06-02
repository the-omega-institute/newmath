import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceDenominatorMonotoneCoverage [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N boundaryRead mediantRead denominatorRead
      toleranceRead streamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg →
      Cont B A boundaryRead →
        Cont boundaryRead M mediantRead →
          Cont mediantRead L denominatorRead →
            Cont denominatorRead T toleranceRead →
              Cont toleranceRead W streamRead →
                PkgSig bundle P pkg →
                  PkgSig bundle N pkg →
                    SemanticNameCert
                      (fun row : BHist => hsame row denominatorRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
                          hsame row T ∨ hsame row denominatorRead ∨ hsame row streamRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont boundaryRead M mediantRead ∧
                          Cont mediantRead L denominatorRead ∧
                            Cont denominatorRead T toleranceRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                      hsame ∧ UnaryHistory boundaryRead ∧ UnaryHistory mediantRead ∧
                        UnaryHistory denominatorRead ∧ UnaryHistory toleranceRead ∧
                          UnaryHistory streamRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier boundaryRoute mediantRoute denominatorRoute toleranceRoute streamRoute
    provenancePkg namePkg
  obtain ⟨bUnary, aUnary, mUnary, lUnary, tUnary, _sUnary, _dUnary, _qUnary, wUnary,
    _rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary, _aEmpty,
    _sEmpty, _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary aUnary boundaryRoute
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed boundaryUnary mUnary mediantRoute
  have denominatorUnary : UnaryHistory denominatorRead :=
    unary_cont_closed mediantUnary lUnary denominatorRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed denominatorUnary tUnary toleranceRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed toleranceUnary wUnary streamRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row denominatorRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨ hsame row T ∨
            hsame row denominatorRead ∨ hsame row streamRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont boundaryRead M mediantRead ∧
            Cont mediantRead L denominatorRead ∧ Cont denominatorRead T toleranceRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro denominatorRead
        ⟨hsame_refl denominatorRead, denominatorUnary⟩
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
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, mediantRoute, denominatorRoute, toleranceRoute, provenancePkg,
          namePkg⟩
  }
  exact
    ⟨cert, boundaryUnary, mediantUnary, denominatorUnary, toleranceUnary, streamUnary⟩

end BEDC.Derived.FareySequenceUp
