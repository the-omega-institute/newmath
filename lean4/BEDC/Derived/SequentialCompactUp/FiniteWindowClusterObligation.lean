import BEDC.Derived.SequentialCompactUp.ObligationReadiness
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactFiniteWindowClusterObligation [AskSetup] [PackageSetup]
    {K B S W R E H C P N sourceRead selectedRead regularRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont K S sourceRead ->
        Cont sourceRead W selectedRead ->
          Cont selectedRead R regularRead ->
            Cont regularRead E sealRead ->
              Cont sealRead N namedRead ->
                PkgSig bundle namedRead pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                        hsame row R ∨ hsame row E ∨ hsame row selectedRead ∨
                          hsame row regularRead ∨ hsame row sealRead ∨
                            hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont K S sourceRead ∧
                        Cont sourceRead W selectedRead ∧
                          Cont selectedRead R regularRead ∧ Cont regularRead E sealRead ∧
                            Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle namedRead pkg)
                    hsame ∧ UnaryHistory sourceRead ∧ UnaryHistory selectedRead ∧
                      UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute selectedRoute regularRoute sealRoute namedRoute namedPkg
  obtain ⟨kUnary, _bUnary, sUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _provenanceUnary, nUnary, _compactBaireStream, _streamWindowRegular,
    _regularSealTransport, _transportReplayProvenance, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed kUnary sUnary sourceRoute
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed sourceUnary wUnary selectedRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed selectedUnary rUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr source.left))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, sourceRoute, selectedRoute, regularRoute, sealRoute,
            namedRoute, provenancePkg, namedPkg⟩
    }
  · exact ⟨sourceUnary, selectedUnary, regularUnary, sealUnary, namedUnary⟩

end BEDC.Derived.SequentialCompactUp
