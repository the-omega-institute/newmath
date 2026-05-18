import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_seven_row_coverage [AskSetup]
    [PackageSetup] {a b c d e f g h p n r : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      (hsame r a ∨ hsame r b ∨ hsame r c ∨ hsame r d ∨ hsame r e ∨ hsame r f ∨
        hsame r g) ->
        UnaryHistory r ∧ (Cont a b h ∧ Cont c d h ∧ Cont e f h) ∧
          (hsame r a ∨ hsame r b ∨ hsame r c ∨ hsame r d ∨ hsame r e ∨
            hsame r f ∨ hsame r g) := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg hsame
  intro packet refusalRow
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, routeCD,
      routeEF, _pUnary, _sameProvenanceName, _pkgSig⟩ := packet
  have rowUnary : UnaryHistory r := by
    cases refusalRow with
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
  exact ⟨rowUnary, ⟨routeAB, routeCD, routeEF⟩, refusalRow⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
