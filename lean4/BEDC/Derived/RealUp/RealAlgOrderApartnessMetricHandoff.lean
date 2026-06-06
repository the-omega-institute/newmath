import BEDC.Derived.ApartnessRealUp

namespace BEDC.Derived.RealUp

open BEDC.Derived.ApartnessRealUp
open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealAlgOrderConstantApartnessMetricHandoff [AskSetup] [PackageSetup]
    {left right radius window leftEndpoint rightEndpoint forwardLedger reverseLedger pkgrow
      metricRow consumerRow scopeRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealSeparationPacket left right radius window leftEndpoint rightEndpoint
        forwardLedger reverseLedger pkgrow bundle pkg →
      UnaryHistory left →
        UnaryHistory right →
          UnaryHistory window →
            UnaryHistory metricRow →
              Cont pkgrow metricRow consumerRow →
                Cont pkgrow window scopeRow →
                  PkgSig bundle consumerRow pkg →
                    PkgSig bundle scopeRow pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row leftEndpoint ∨ hsame row rightEndpoint ∨
                                hsame row radius) ∧
                              UnaryHistory row)
                          (fun row : BHist =>
                            hsame row leftEndpoint ∨ hsame row rightEndpoint ∨
                              hsame row radius ∨ hsame row window ∨
                                hsame row consumerRow ∨ hsame row scopeRow)
                          (fun _row : BHist => PkgSig bundle consumerRow pkg)
                          hsame ∧
                        PositiveUnaryDenominator radius ∧ UnaryHistory consumerRow := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet leftUnary rightUnary windowUnary metricUnary consumerCont _scopeCont
    consumerPkg _scopePkg
  have positiveRadius : PositiveUnaryDenominator radius :=
    packet.left
  have radiusUnary : UnaryHistory radius :=
    (PositiveUnaryDenominator_unary_and_nonempty positiveRadius).left
  have leftEndpointCont : Cont left window leftEndpoint :=
    packet.right.left
  have rightEndpointCont : Cont right window rightEndpoint :=
    packet.right.right.left
  have forwardLedgerCont : Cont leftEndpoint rightEndpoint forwardLedger :=
    packet.right.right.right.left
  have reverseLedgerCont : Cont rightEndpoint leftEndpoint reverseLedger :=
    packet.right.right.right.right.left
  have pkgrowCont : Cont forwardLedger reverseLedger pkgrow :=
    packet.right.right.right.right.right.left
  have leftEndpointUnary : UnaryHistory leftEndpoint :=
    unary_cont_closed leftUnary windowUnary leftEndpointCont
  have rightEndpointUnary : UnaryHistory rightEndpoint :=
    unary_cont_closed rightUnary windowUnary rightEndpointCont
  have forwardLedgerUnary : UnaryHistory forwardLedger :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary forwardLedgerCont
  have reverseLedgerUnary : UnaryHistory reverseLedger :=
    unary_cont_closed rightEndpointUnary leftEndpointUnary reverseLedgerCont
  have pkgrowUnary : UnaryHistory pkgrow :=
    unary_cont_closed forwardLedgerUnary reverseLedgerUnary pkgrowCont
  have consumerUnary : UnaryHistory consumerRow :=
    unary_cont_closed pkgrowUnary metricUnary consumerCont
  have sourceLeftEndpoint :
      (fun row : BHist =>
        (hsame row leftEndpoint ∨ hsame row rightEndpoint ∨ hsame row radius) ∧
          UnaryHistory row) leftEndpoint := by
    exact ⟨Or.inl (hsame_refl leftEndpoint), leftEndpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row leftEndpoint ∨ hsame row rightEndpoint ∨ hsame row radius) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row leftEndpoint ∨ hsame row rightEndpoint ∨ hsame row radius ∨
              hsame row window ∨ hsame row consumerRow ∨ hsame row scopeRow)
          (fun _row : BHist => PkgSig bundle consumerRow pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro leftEndpoint sourceLeftEndpoint
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
        have sameOtherRow : hsame _other _row := hsame_symm sameRows
        have transported :
            hsame _other leftEndpoint ∨ hsame _other rightEndpoint ∨
              hsame _other radius := by
          cases source.left with
          | inl sameLeft =>
              exact Or.inl (hsame_trans sameOtherRow sameLeft)
          | inr rest =>
              cases rest with
              | inl sameRight =>
                  exact Or.inr (Or.inl (hsame_trans sameOtherRow sameRight))
              | inr sameRadius =>
                  exact Or.inr (Or.inr (hsame_trans sameOtherRow sameRadius))
        exact ⟨transported, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameLeft =>
          exact Or.inl sameLeft
      | inr rest =>
          cases rest with
          | inl sameRight =>
              exact Or.inr (Or.inl sameRight)
          | inr sameRadius =>
              exact Or.inr (Or.inr (Or.inl sameRadius))
    ledger_sound := by
      intro _row _source
      exact consumerPkg
  }
  exact ⟨cert, positiveRadius, consumerUnary⟩

end BEDC.Derived.RealUp
