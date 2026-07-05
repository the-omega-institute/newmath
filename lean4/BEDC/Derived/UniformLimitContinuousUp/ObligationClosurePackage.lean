import BEDC.Derived.UniformLimitContinuousUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformLimitContinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformLimitContinuousCarrier [AskSetup] [PackageSetup]
    (F U M W R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory F ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory W ∧
    UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont F U M ∧ Cont M W R ∧
        Cont R E H ∧ Cont H C N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem UniformLimitContinuousObligationClosurePackage [AskSetup] [PackageSetup]
    {F U M W R E H C P N familyRead _limitRead modulusRead regularRead endpointRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformLimitContinuousCarrier F U M W R E H C P N bundle pkg →
      Cont F U familyRead →
        Cont familyRead M modulusRead →
          Cont modulusRead W regularRead →
            Cont regularRead E endpointRead →
              Cont endpointRead N publicRead →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row F ∨ hsame row U ∨ hsame row M ∨ hsame row W ∨
                          hsame row R ∨ hsame row E ∨ hsame row endpointRead ∨
                            hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont F U familyRead ∧
                          Cont familyRead M modulusRead ∧
                            Cont modulusRead W regularRead ∧
                              Cont regularRead E endpointRead ∧
                                Cont endpointRead N publicRead ∧
                                  PkgSig bundle publicRead pkg)
                      hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier familyRoute modulusRoute regularRoute endpointRoute publicRoute publicPkg
  obtain ⟨fUnary, uUnary, mUnary, wUnary, _rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _familyCarrierRoute, _regularCarrierRoute, _endpointCarrierRoute,
    _publicCarrierRoute, _provenancePkg, _namePkg⟩ := carrier
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed fUnary uUnary familyRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed familyUnary mUnary modulusRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed modulusUnary wUnary regularRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed regularUnary eUnary endpointRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary nUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row U ∨ hsame row M ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row endpointRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F U familyRead ∧ Cont familyRead M modulusRead ∧
              Cont modulusRead W regularRead ∧ Cont regularRead E endpointRead ∧
                Cont endpointRead N publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, familyRoute, modulusRoute, regularRoute, endpointRoute, publicRoute,
          publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.UniformLimitContinuousUp
