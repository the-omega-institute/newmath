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

theorem CompactCoverLebesgueLedgerCarrier_uniform_modulus_handoff [AskSetup] [PackageSetup]
    {compactNet pointwiseRadius ratLedger lowerBoundFold uniformModulus transport route
      provenance name uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory lowerBoundFold ->
      UnaryHistory uniformModulus ->
        Cont lowerBoundFold uniformModulus uniformRead ->
          PkgSig bundle provenance pkg ->
            compactCoverLebesgueLedgerFields
                (CompactCoverLebesgueLedgerUp.mk compactNet pointwiseRadius ratLedger
                  lowerBoundFold uniformModulus transport route provenance name) =
              [compactNet, pointwiseRadius, ratLedger, lowerBoundFold, uniformModulus,
                transport, route, provenance, name] ∧
              UnaryHistory uniformRead ∧
                Cont lowerBoundFold uniformModulus uniformRead ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: CompactCoverLebesgueLedgerUp BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro lowerUnary uniformUnary uniformReadRow provenancePkg
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed lowerUnary uniformUnary uniformReadRow
  exact ⟨rfl, uniformReadUnary, uniformReadRow, provenancePkg⟩

end BEDC.Derived.CompactCoverLebesgueLedgerUp
