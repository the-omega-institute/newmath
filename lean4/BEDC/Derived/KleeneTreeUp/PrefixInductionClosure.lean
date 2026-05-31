import BEDC.Derived.KleeneTreeUp.NameCertObligations

namespace BEDC.Derived.KleeneTreeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KleeneTreeCarrier_prefix_induction_closure [AskSetup] [PackageSetup]
    {tree boolLedger listSpine stream obstruction transport traversal provenance localName
      parentRead nodeRead closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KleeneTreeCarrier tree boolLedger listSpine stream obstruction transport traversal provenance
        localName bundle pkg ->
      Cont listSpine tree parentRead ->
        Cont parentRead boolLedger nodeRead ->
          Cont nodeRead obstruction closureRead ->
            PkgSig bundle closureRead pkg ->
              UnaryHistory listSpine ∧ UnaryHistory tree ∧ UnaryHistory boolLedger ∧
                UnaryHistory obstruction ∧ UnaryHistory parentRead ∧ UnaryHistory nodeRead ∧
                  UnaryHistory closureRead ∧ Cont listSpine tree parentRead ∧
                    Cont parentRead boolLedger nodeRead ∧
                      Cont nodeRead obstruction closureRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle closureRead pkg := by
  -- BEDC touchpoint anchor: KleeneTreeCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier listTree parentBool nodeObstruction closurePkg
  obtain ⟨treeUnary, boolUnary, listUnary, _streamUnary, obstructionUnary, _transportUnary,
    _traversalUnary, _provenanceUnary, _localNameUnary, provenancePkg, _localNamePkg⟩ :=
    carrier
  have parentUnary : UnaryHistory parentRead :=
    unary_cont_closed listUnary treeUnary listTree
  have nodeUnary : UnaryHistory nodeRead :=
    unary_cont_closed parentUnary boolUnary parentBool
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed nodeUnary obstructionUnary nodeObstruction
  exact
    ⟨listUnary, treeUnary, boolUnary, obstructionUnary, parentUnary, nodeUnary, closureUnary,
      listTree, parentBool, nodeObstruction, provenancePkg, closurePkg⟩

end BEDC.Derived.KleeneTreeUp
