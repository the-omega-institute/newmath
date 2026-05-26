import BEDC.Derived.CauchyProductUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_constant_right_factor [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name constantWindow constantObservation realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      hsame constantWindow windowB ->
        Cont constantWindow radiusB constantObservation ->
          Cont classifier routes realSeal ->
            PkgSig bundle realSeal pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row constantWindow ∨ hsame row constantObservation ∨
                      hsame row product ∨ hsame row classifier ∨ hsame row realSeal)
                  (fun row : BHist =>
                    hsame row constantWindow ∨ hsame row constantObservation ∨
                      hsame row product ∨ hsame row classifier ∨ hsame row realSeal)
                  (fun row : BHist =>
                    PkgSig bundle realSeal pkg ∧
                      (hsame row constantWindow ∨ hsame row constantObservation ∨
                        hsame row product ∨ hsame row classifier ∨ hsame row realSeal))
                  hsame ∧
                UnaryHistory constantWindow ∧ UnaryHistory constantObservation ∧
                  UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory realSeal ∧
                    Cont constantWindow radiusB constantObservation ∧
                      Cont observationA observationB product ∧ Cont product ledger classifier ∧
                        Cont classifier routes realSeal ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet sameConstantWindow constantWindowObservation classifierRoutesRealSeal
    realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, windowBUnary, _radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have constantWindowUnary : UnaryHistory constantWindow :=
    unary_transport windowBUnary (hsame_symm sameConstantWindow)
  have constantObservationUnary : UnaryHistory constantObservation :=
    unary_cont_closed constantWindowUnary radiusBUnary constantWindowObservation
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRealSeal
  have sourceAtConstantWindow :
      hsame constantWindow constantWindow ∨ hsame constantWindow constantObservation ∨
        hsame constantWindow product ∨ hsame constantWindow classifier ∨
          hsame constantWindow realSeal :=
    Or.inl (hsame_refl constantWindow)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row constantWindow ∨ hsame row constantObservation ∨ hsame row product ∨
              hsame row classifier ∨ hsame row realSeal)
          (fun row : BHist =>
            hsame row constantWindow ∨ hsame row constantObservation ∨ hsame row product ∨
              hsame row classifier ∨ hsame row realSeal)
          (fun row : BHist =>
            PkgSig bundle realSeal pkg ∧
              (hsame row constantWindow ∨ hsame row constantObservation ∨
                hsame row product ∨ hsame row classifier ∨ hsame row realSeal))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro constantWindow sourceAtConstantWindow
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
        intro row row' sameRows source
        cases source with
        | inl sameConstant =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameConstant)
        | inr rest =>
            cases rest with
            | inl sameObservation =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameObservation))
            | inr rest =>
                cases rest with
                | inl sameProduct =>
                    exact
                      Or.inr (Or.inr (Or.inl
                        (hsame_trans (hsame_symm sameRows) sameProduct)))
                | inr rest =>
                    cases rest with
                    | inl sameClassifier =>
                        exact
                          Or.inr (Or.inr (Or.inr (Or.inl
                            (hsame_trans (hsame_symm sameRows) sameClassifier))))
                    | inr sameSeal =>
                        exact
                          Or.inr (Or.inr (Or.inr (Or.inr
                            (hsame_trans (hsame_symm sameRows) sameSeal))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨realSealPkg, source⟩
  }
  exact
    ⟨cert, constantWindowUnary, constantObservationUnary, productUnary, classifierUnary,
      realSealUnary, constantWindowObservation, productRoute, classifierRoute,
      classifierRoutesRealSeal, namePkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
