import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_registry_classifier_scope [AskSetup]
    [PackageSetup] {a b c d e f g h p n r classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      (hsame r a ∨ hsame r b ∨ hsame r c ∨ hsame r d ∨ hsame r e ∨ hsame r f ∨
          hsame r g) ->
        Cont r h classifierRead ->
          PkgSig bundle classifierRead pkg ->
            UnaryHistory r ∧ UnaryHistory h ∧ UnaryHistory classifierRead ∧
              Cont r h classifierRead ∧ PkgSig bundle p pkg ∧
                PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame PkgSig
  intro packet registryRow registryClassifierRead classifierPkg
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, _routeCD,
      _routeEF, _pUnary, _sameProvenanceName, provenancePkg⟩ := packet
  have rUnary : UnaryHistory r := by
    cases registryRow with
    | inl sameA =>
        exact unary_transport_symm aUnary sameA
    | inr rest =>
        cases rest with
        | inl sameB =>
            exact unary_transport_symm bUnary sameB
        | inr rest =>
            cases rest with
            | inl sameC =>
                exact unary_transport_symm cUnary sameC
            | inr rest =>
                cases rest with
                | inl sameD =>
                    exact unary_transport_symm dUnary sameD
                | inr rest =>
                    cases rest with
                    | inl sameE =>
                        exact unary_transport_symm eUnary sameE
                    | inr rest =>
                        cases rest with
                        | inl sameF =>
                            exact unary_transport_symm fUnary sameF
                        | inr sameG =>
                            exact unary_transport_symm gUnary sameG
  have hUnary : UnaryHistory h :=
    unary_cont_closed aUnary bUnary routeAB
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed rUnary hUnary registryClassifierRead
  exact
    ⟨rUnary, hUnary, classifierReadUnary, registryClassifierRead, provenancePkg,
      classifierPkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
