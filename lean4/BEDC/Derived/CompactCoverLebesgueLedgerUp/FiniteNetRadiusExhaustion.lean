import BEDC.Derived.CompactCoverLebesgueLedgerUp.UniformModulusHandoff

namespace BEDC.Derived.CompactCoverLebesgueLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactCoverLebesgueLedgerCarrier_finite_net_radius_exhaustion
    [AskSetup] [PackageSetup]
    {compactNet pointwiseRadius ratLedger lowerBoundFold uniformModulus transport route
      provenance name uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory compactNet ->
      UnaryHistory pointwiseRadius ->
        UnaryHistory ratLedger ->
          UnaryHistory lowerBoundFold ->
            UnaryHistory uniformModulus ->
              Cont compactNet pointwiseRadius ratLedger ->
                Cont ratLedger lowerBoundFold uniformRead ->
                  PkgSig bundle provenance pkg ->
                    compactCoverLebesgueLedgerFields
                        (CompactCoverLebesgueLedgerUp.mk compactNet pointwiseRadius
                          ratLedger lowerBoundFold uniformModulus transport route
                          provenance name) =
                      [compactNet, pointwiseRadius, ratLedger, lowerBoundFold,
                        uniformModulus, transport, route, provenance, name] ∧
                      UnaryHistory uniformRead ∧
                        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro _compactNetUnary _pointwiseRadiusUnary ratLedgerUnary lowerBoundFoldUnary
    _uniformModulusUnary _radiusLedgerRoute uniformReadRoute provenancePkg
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed ratLedgerUnary lowerBoundFoldUnary uniformReadRoute
  exact ⟨rfl, uniformReadUnary, provenancePkg⟩

end BEDC.Derived.CompactCoverLebesgueLedgerUp
