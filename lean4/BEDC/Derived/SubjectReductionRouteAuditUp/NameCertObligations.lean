import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubjectReductionRouteAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubjectReductionRouteAudit_namecert_obligations [AskSetup] [PackageSetup]
    {B E I U S H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory E ->
        UnaryHistory I ->
          UnaryHistory U ->
            UnaryHistory S ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      PkgSig bundle P pkg ->
                        PkgSig bundle N pkg ->
                          SemanticNameCert
                            (fun row : BHist => hsame row N /\ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row B \/ hsame row E \/ hsame row I \/
                                hsame row U \/ hsame row S \/ hsame row H \/
                                  hsame row C \/ hsame row P \/ hsame row N)
                            (fun row : BHist =>
                              UnaryHistory row /\ PkgSig bundle P pkg /\
                                PkgSig bundle N pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro _unaryB _unaryE _unaryI _unaryU _unaryS _unaryH _unaryC _unaryP unaryN
    pkgP pkgN
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, unaryN⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgP, pkgN⟩
  }

end BEDC.Derived.SubjectReductionRouteAuditUp
