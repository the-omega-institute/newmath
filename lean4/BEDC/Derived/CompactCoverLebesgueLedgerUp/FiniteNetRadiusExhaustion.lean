import BEDC.Derived.CompactCoverLebesgueLedgerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactCoverLebesgueLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactCoverLebesgueLedgerFiniteNetRadiusExhaustion [AskSetup] [PackageSetup]
    {compactNet pointwiseRadius ratLedger lowerBoundFold uniformModulus transport route
      provenance name finiteNetRead radiusRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory compactNet →
      UnaryHistory pointwiseRadius →
        UnaryHistory ratLedger →
          UnaryHistory lowerBoundFold →
            Cont compactNet pointwiseRadius finiteNetRead →
              Cont finiteNetRead ratLedger radiusRead →
                Cont radiusRead lowerBoundFold uniformRead →
                  PkgSig bundle provenance pkg →
                    compactCoverLebesgueLedgerFields
                        (CompactCoverLebesgueLedgerUp.mk compactNet pointwiseRadius
                          ratLedger lowerBoundFold uniformModulus transport route provenance
                          name) =
                      [compactNet, pointwiseRadius, ratLedger, lowerBoundFold,
                        uniformModulus, transport, route, provenance, name] ∧
                      UnaryHistory finiteNetRead ∧ UnaryHistory radiusRead ∧
                        UnaryHistory uniformRead ∧
                          Cont compactNet pointwiseRadius finiteNetRead ∧
                            Cont finiteNetRead ratLedger radiusRead ∧
                              Cont radiusRead lowerBoundFold uniformRead ∧
                                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: CompactCoverLebesgueLedgerUp BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro unaryCompactNet unaryPointwiseRadius unaryRatLedger unaryLowerBoundFold
    routeFiniteNet routeRadius routeUniform provenancePkg
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed unaryCompactNet unaryPointwiseRadius routeFiniteNet
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed finiteNetUnary unaryRatLedger routeRadius
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed radiusUnary unaryLowerBoundFold routeUniform
  exact
    ⟨rfl, finiteNetUnary, radiusUnary, uniformUnary, routeFiniteNet, routeRadius,
      routeUniform, provenancePkg⟩

end BEDC.Derived.CompactCoverLebesgueLedgerUp
