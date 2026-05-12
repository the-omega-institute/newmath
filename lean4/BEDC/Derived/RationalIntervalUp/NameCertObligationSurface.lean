import BEDC.Derived.RationalIntervalUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RationalIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint left' right' order'
      containment' transport' route' provenance' name' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      RationalIntervalPacket left' right' order' containment' transport' route' provenance' name'
          endpoint' bundle pkg ->
        hsame left left' ->
          hsame right right' ->
            hsame containment containment' ->
              hsame route route' ->
                hsame name name' ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row endpoint' ∧
                          RationalIntervalPacket left' right' order' containment' transport'
                            route' provenance' name' row bundle pkg)
                      (fun row : BHist => UnaryHistory row ∧ Cont provenance' name' row)
                      (fun row : BHist => PkgSig bundle row pkg ∧ UnaryHistory provenance')
                      (fun row row' : BHist => psame bundle pkg pkg ∧ hsame row row') ∧
                    hsame order order' ∧ hsame transport transport' ∧
                      hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro packet packet' sameLeft sameRight sameContainment sameRoute sameName
  obtain ⟨_leftUnary', _rightUnary', _orderUnary', _containmentUnary', _transportUnary',
    _routeUnary', provenanceUnary', _nameUnary', _endpointUnary', leftRightOrder',
    orderContainmentTransport', transportRouteProvenance', provenanceNameEndpoint',
    endpointPkg'⟩ := packet'
  have transported :=
    RationalIntervalPacket_endpoint_containment_transport packet sameLeft sameRight
      sameContainment sameRoute sameName leftRightOrder' orderContainmentTransport'
      transportRouteProvenance' provenanceNameEndpoint' endpointPkg'
  have sameOrder : hsame order order' := transported.right.left
  have sameTransport : hsame transport transport' := transported.right.right.left
  have sameProvenance : hsame provenance provenance' := transported.right.right.right.left
  have sameEndpoint : hsame endpoint endpoint' := transported.right.right.right.right
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row endpoint' ∧
            RationalIntervalPacket left' right' order' containment' transport' route'
              provenance' name' row bundle pkg)
        (fun row : BHist => UnaryHistory row ∧ Cont provenance' name' row)
        (fun row : BHist => PkgSig bundle row pkg ∧ UnaryHistory provenance')
        (fun row row' : BHist => psame bundle pkg pkg ∧ hsame row row') := {
    core := {
      carrier_inhabited := Exists.intro endpoint' ⟨hsame_refl endpoint', transported.left⟩
      equiv_refl := by
        intro row sourceRow
        obtain ⟨_sameRow, rowPacket⟩ := sourceRow
        obtain ⟨_leftUnary, _rightUnary, _orderUnary, _containmentUnary, _transportUnary,
          _routeUnary, _provenanceUnary, _nameUnary, _rowUnary, _leftRightOrder,
          _orderContainmentTransport, _transportRouteProvenance, _provenanceNameEndpoint,
          rowPkg⟩ := rowPacket
        exact ⟨PkgSig_psame_intro rowPkg rowPkg (hsame_refl row), hsame_refl row⟩
      equiv_symm := by
        intro _row _row' classified
        exact ⟨classified.left, hsame_symm classified.right⟩
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified.right
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      obtain ⟨_sameRow, rowPacket⟩ := sourceRow
      obtain ⟨_leftUnary, _rightUnary, _orderUnary, _containmentUnary, _transportUnary,
        _routeUnary, _provenanceUnary, _nameUnary, rowUnary, _leftRightOrder,
        _orderContainmentTransport, _transportRouteProvenance, provenanceNameRow,
        _rowPkg⟩ := rowPacket
      exact ⟨rowUnary, provenanceNameRow⟩
    ledger_sound := by
      intro _row sourceRow
      obtain ⟨_sameRow, rowPacket⟩ := sourceRow
      obtain ⟨_leftUnary, _rightUnary, _orderUnary, _containmentUnary, _transportUnary,
        _routeUnary, provenanceUnary, _nameUnary, _rowUnary, _leftRightOrder,
        _orderContainmentTransport, _transportRouteProvenance, _provenanceNameEndpoint,
        rowPkg⟩ := rowPacket
      exact ⟨rowPkg, provenanceUnary⟩
  }
  exact ⟨cert, sameOrder, sameTransport, sameProvenance, sameEndpoint⟩

end BEDC.Derived.RationalIntervalUp
