import BEDC.Derived.SynchronizationCertificateUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SynchronizationCertificateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SynchronizationCertificate_locality [AskSetup] [PackageSetup]
    {x : SynchronizationCertificateUp}
    {Hi Hj Ti Tj R L S C P N routeI routeJ localRoute refusalRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    synchronizationCertificateFields x = [Hi, Hj, Ti, Tj, R, L, S, C, P, N] ->
      Cont Hi Ti routeI ->
        Cont Hj Tj routeJ ->
          Cont R L localRoute ->
            Cont localRoute S refusalRoute ->
              UnaryHistory Hi ->
                UnaryHistory Hj ->
                  UnaryHistory Ti ->
                    UnaryHistory Tj ->
                      UnaryHistory R ->
                        UnaryHistory L ->
                          UnaryHistory S ->
                            PkgSig bundle N pkg ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row refusalRoute ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row refusalRoute ∧ Cont Hi Ti routeI ∧
                                      Cont Hj Tj routeJ ∧ Cont R L localRoute ∧
                                        Cont localRoute S refusalRoute)
                                  (fun row : BHist =>
                                    hsame row refusalRoute ∧ PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory routeI ∧ UnaryHistory routeJ ∧
                                  UnaryHistory localRoute ∧ UnaryHistory refusalRoute := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fields sourceRoute targetRoute localityRoute refusalCont sourceUnary targetUnary
    sourceStreamUnary targetStreamUnary correspondenceUnary localityUnary refusalUnary namePkg
  have _fields :
      synchronizationCertificateFields x = [Hi, Hj, Ti, Tj, R, L, S, C, P, N] := fields
  have routeIUnary : UnaryHistory routeI :=
    unary_cont_closed sourceUnary sourceStreamUnary sourceRoute
  have routeJUnary : UnaryHistory routeJ :=
    unary_cont_closed targetUnary targetStreamUnary targetRoute
  have localRouteUnary : UnaryHistory localRoute :=
    unary_cont_closed correspondenceUnary localityUnary localityRoute
  have refusalRouteUnary : UnaryHistory refusalRoute :=
    unary_cont_closed localRouteUnary refusalUnary refusalCont
  have sourceAtRefusal : hsame refusalRoute refusalRoute ∧ UnaryHistory refusalRoute :=
    ⟨hsame_refl refusalRoute, refusalRouteUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRoute ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row refusalRoute ∧ Cont Hi Ti routeI ∧ Cont Hj Tj routeJ ∧
              Cont R L localRoute ∧ Cont localRoute S refusalRoute)
          (fun row : BHist => hsame row refusalRoute ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRoute sourceAtRefusal
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, sourceRoute, targetRoute, localityRoute, refusalCont⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }
  exact ⟨cert, routeIUnary, routeJUnary, localRouteUnary, refusalRouteUnary⟩

end BEDC.Derived.SynchronizationCertificateUp
