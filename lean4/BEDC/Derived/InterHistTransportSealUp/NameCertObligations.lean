import BEDC.Derived.InterHistTransportSealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.InterHistTransportSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem InterHistTransportSeal_namecert_obligations [AskSetup] [PackageSetup]
    {source target locality invariant observer route _transport _continuation _provenance
      _name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory target ->
        UnaryHistory locality ->
          UnaryHistory invariant ->
            UnaryHistory observer ->
              UnaryHistory route ->
                Cont locality invariant observer ->
                  Cont observer route endpoint ->
                    PkgSig bundle endpoint pkg ->
                      SemanticNameCert
                        (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row endpoint ∧ Cont locality invariant observer ∧
                            Cont observer route endpoint)
                        (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _sourceUnary _targetUnary localityUnary invariantUnary observerUnary routeUnary
    localityInvariant observerRoute endpointPkg
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed observerUnary routeUnary observerRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
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
      exact ⟨source.left, localityInvariant, observerRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, endpointPkg⟩
  }

end BEDC.Derived.InterHistTransportSealUp
