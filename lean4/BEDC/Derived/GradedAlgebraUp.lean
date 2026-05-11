import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GradedAlgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GradedAlgebraBHistSource (row : BHist) : Prop :=
  exists base degree component product provenance : BHist,
    Cont base degree component ∧
      Cont component product provenance ∧ hsame row (BHist.e0 provenance)

def GradedAlgebraDegreePattern (row : BHist) : Prop :=
  exists base degree component provenance : BHist,
    Cont base degree component ∧ hsame row (BHist.e0 provenance)

def GradedAlgebraProductLedger (row : BHist) : Prop :=
  exists component product provenance : BHist,
    Cont component product provenance ∧ hsame row (BHist.e0 provenance)

theorem GradedAlgebraPacket_namecert_obligation_surface :
    SemanticNameCert GradedAlgebraBHistSource GradedAlgebraDegreePattern
      GradedAlgebraProductLedger hsame := by
  have source : GradedAlgebraBHistSource (BHist.e0 BHist.Empty) := by
    exact Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (Exists.intro BHist.Empty
            (Exists.intro BHist.Empty
              (And.intro (cont_left_unit BHist.Empty)
                (And.intro (cont_left_unit BHist.Empty)
                  (hsame_refl (BHist.e0 BHist.Empty))))))))
  constructor
  · constructor
    · exact Exists.intro (BHist.e0 BHist.Empty) source
    · intro row _source
      exact hsame_refl row
    · intro left right sameRows
      exact hsame_symm sameRows
    · intro left middle right sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro left right sameRows sourceLeft
      cases sourceLeft with
      | intro base baseData =>
          cases baseData with
          | intro degree degreeData =>
              cases degreeData with
              | intro component componentData =>
                  cases componentData with
                  | intro product productData =>
                      cases productData with
                      | intro provenance packet =>
                          exact Exists.intro base
                            (Exists.intro degree
                              (Exists.intro component
                                (Exists.intro product
                                  (Exists.intro provenance
                                    (And.intro packet.left
                                      (And.intro packet.right.left
                                        (hsame_trans (hsame_symm sameRows)
                                          packet.right.right)))))))
  · intro row sourceRow
    cases sourceRow with
    | intro base baseData =>
        cases baseData with
        | intro degree degreeData =>
            cases degreeData with
            | intro component componentData =>
                cases componentData with
                | intro product productData =>
                    cases productData with
                    | intro provenance packet =>
                        exact Exists.intro base
                          (Exists.intro degree
                            (Exists.intro component
                              (Exists.intro provenance
                                (And.intro packet.left packet.right.right))))
  · intro row sourceRow
    cases sourceRow with
    | intro base baseData =>
        cases baseData with
        | intro degree degreeData =>
            cases degreeData with
            | intro component componentData =>
                cases componentData with
                | intro product productData =>
                    cases productData with
                    | intro provenance packet =>
                        exact Exists.intro component
                          (Exists.intro product
                            (Exists.intro provenance
                              (And.intro packet.right.left packet.right.right)))

def GradedAlgebraPacket [AskSetup] [PackageSetup]
    (ring degree component multiplication action provenance product moduleRead endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory ring ∧ UnaryHistory degree ∧ UnaryHistory component ∧
    UnaryHistory multiplication ∧ UnaryHistory action ∧ UnaryHistory provenance ∧
      UnaryHistory product ∧ UnaryHistory moduleRead ∧ UnaryHistory endpoint ∧
        Cont ring degree component ∧ Cont component multiplication product ∧
          Cont product action moduleRead ∧ Cont moduleRead provenance endpoint ∧
            PkgSig bundle endpoint pkg

theorem GradedAlgebraPacket_component_stability [AskSetup] [PackageSetup]
    {ring degree component multiplication action provenance product moduleRead endpoint
      ring' degree' component' multiplication' action' provenance' product' moduleRead'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GradedAlgebraPacket ring degree component multiplication action provenance product
        moduleRead endpoint bundle pkg ->
      hsame ring ring' -> hsame degree degree' -> hsame component component' ->
        hsame multiplication multiplication' -> hsame action action' ->
          hsame provenance provenance' -> Cont ring' degree' component' ->
            Cont component' multiplication' product' ->
              Cont product' action' moduleRead' ->
                Cont moduleRead' provenance' endpoint' ->
                  PkgSig bundle endpoint' pkg ->
                    GradedAlgebraPacket ring' degree' component' multiplication' action'
                        provenance' product' moduleRead' endpoint' bundle pkg ∧
                      hsame product product' ∧ hsame moduleRead moduleRead' ∧
                        hsame endpoint endpoint' := by
  intro packet sameRing sameDegree sameComponent sameMultiplication sameAction sameProvenance
    componentCont' productCont' moduleCont' endpointCont' pkgSig'
  have ringUnary' : UnaryHistory ring' :=
    unary_transport packet.left sameRing
  have degreeUnary' : UnaryHistory degree' :=
    unary_transport packet.right.left sameDegree
  have componentUnary' : UnaryHistory component' :=
    unary_transport packet.right.right.left sameComponent
  have multiplicationUnary' : UnaryHistory multiplication' :=
    unary_transport packet.right.right.right.left sameMultiplication
  have actionUnary' : UnaryHistory action' :=
    unary_transport packet.right.right.right.right.left sameAction
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.right.right.left sameProvenance
  have sameProduct : hsame product product' :=
    cont_respects_hsame sameComponent sameMultiplication
      packet.right.right.right.right.right.right.right.right.right.right.left productCont'
  have productUnary' : UnaryHistory product' :=
    unary_transport packet.right.right.right.right.right.right.left sameProduct
  have sameModuleRead : hsame moduleRead moduleRead' :=
    cont_respects_hsame sameProduct sameAction
      packet.right.right.right.right.right.right.right.right.right.right.right.left moduleCont'
  have moduleReadUnary' : UnaryHistory moduleRead' :=
    unary_transport packet.right.right.right.right.right.right.right.left sameModuleRead
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameModuleRead sameProvenance
      packet.right.right.right.right.right.right.right.right.right.right.right.right.left
      endpointCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport packet.right.right.right.right.right.right.right.right.left sameEndpoint
  exact And.intro
    (And.intro ringUnary'
      (And.intro degreeUnary'
        (And.intro componentUnary'
          (And.intro multiplicationUnary'
            (And.intro actionUnary'
              (And.intro provenanceUnary'
                (And.intro productUnary'
                  (And.intro moduleReadUnary'
                    (And.intro endpointUnary'
                      (And.intro componentCont'
                        (And.intro productCont'
                          (And.intro moduleCont'
                            (And.intro endpointCont' pkgSig')))))))))))))
    (And.intro sameProduct (And.intro sameModuleRead sameEndpoint))

theorem GradedAlgebraPacket_product_ledger [AskSetup] [PackageSetup]
    {ring degree component multiplication action provenance product moduleRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GradedAlgebraPacket ring degree component multiplication action provenance product
        moduleRead endpoint bundle pkg ->
      Cont component multiplication product ->
        Cont product action moduleRead ->
          Cont moduleRead provenance endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory component ∧ UnaryHistory multiplication ∧ UnaryHistory action ∧
                UnaryHistory product ∧ UnaryHistory moduleRead ∧ UnaryHistory endpoint ∧
                  Cont component multiplication product ∧ Cont product action moduleRead ∧
                    Cont moduleRead provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet productRow moduleRow endpointRow pkgRow
  have componentUnary : UnaryHistory component :=
    packet.right.right.left
  have multiplicationUnary : UnaryHistory multiplication :=
    packet.right.right.right.left
  have actionUnary : UnaryHistory action :=
    packet.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.right.left
  have productUnary : UnaryHistory product :=
    unary_cont_closed componentUnary multiplicationUnary productRow
  have moduleReadUnary : UnaryHistory moduleRead :=
    unary_cont_closed productUnary actionUnary moduleRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed moduleReadUnary provenanceUnary endpointRow
  exact
    ⟨componentUnary, multiplicationUnary, actionUnary, productUnary, moduleReadUnary,
      endpointUnary, productRow, moduleRow, endpointRow, pkgRow⟩

end BEDC.Derived.GradedAlgebraUp
