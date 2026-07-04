import BEDC.Derived.SubjectReductionRouteAuditUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubjectReductionRouteAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubjectReductionRouteAudit_socket_handoff [AskSetup] [PackageSetup]
    {B E I U S H C P N exactRead invokeRead socketRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory E ->
        UnaryHistory I ->
          UnaryHistory U ->
            UnaryHistory S ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont B E exactRead ->
                        Cont exactRead I invokeRead ->
                          Cont U S socketRead ->
                            Cont invokeRead socketRead namedRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row namedRead /\ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row B \/ hsame row E \/ hsame row I \/
                                          hsame row U \/ hsame row S \/ hsame row H \/
                                            hsame row C \/ hsame row P \/ hsame row N \/
                                              hsame row exactRead \/ hsame row invokeRead \/
                                                hsame row socketRead \/ hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row /\ Cont B E exactRead /\
                                          Cont exactRead I invokeRead /\ Cont U S socketRead /\
                                            Cont invokeRead socketRead namedRead /\
                                              PkgSig bundle P pkg /\ PkgSig bundle N pkg)
                                      hsame /\
                                    UnaryHistory exactRead /\ UnaryHistory invokeRead /\
                                      UnaryHistory socketRead /\ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryB unaryE unaryI unaryU unaryS _unaryH _unaryC _unaryP _unaryN
    exactRoute invokeRoute socketRoute namedRoute pkgP pkgN
  have exactUnary : UnaryHistory exactRead :=
    unary_cont_closed unaryB unaryE exactRoute
  have invokeUnary : UnaryHistory invokeRead :=
    unary_cont_closed exactUnary unaryI invokeRoute
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed unaryU unaryS socketRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed invokeUnary socketUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row B \/ hsame row E \/ hsame row I \/ hsame row U \/ hsame row S \/
              hsame row H \/ hsame row C \/ hsame row P \/ hsame row N \/
                hsame row exactRead \/ hsame row invokeRead \/ hsame row socketRead \/
                  hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row /\ Cont B E exactRead /\ Cont exactRead I invokeRead /\
              Cont U S socketRead /\ Cont invokeRead socketRead namedRead /\
                PkgSig bundle P pkg /\ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, exactRoute, invokeRoute, socketRoute, namedRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, exactUnary, invokeUnary, socketUnary, namedUnary⟩

theorem SubjectReductionRouteAudit_discharge_boundary [AskSetup] [PackageSetup]
    {B E I U S H C P N exactRead invokeRead socketRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B →
      UnaryHistory E →
        UnaryHistory I →
          UnaryHistory U →
            UnaryHistory S →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory N →
                      Cont B E exactRead →
                        Cont exactRead I invokeRead →
                          Cont U S socketRead →
                            Cont invokeRead socketRead namedRead →
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  (∃ packet : BEDC.Derived.SubjectReductionRouteAuditUp,
                                      packet =
                                        BEDC.Derived.SubjectReductionRouteAuditUp.mk
                                          B E I U S H C P N) ∧
                                    SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row B ∨ hsame row E ∨ hsame row I ∨
                                          hsame row U ∨ hsame row S ∨ hsame row H ∨
                                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                                              hsame row exactRead ∨ hsame row invokeRead ∨
                                                hsame row socketRead ∨ hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont B E exactRead ∧
                                          Cont exactRead I invokeRead ∧ Cont U S socketRead ∧
                                            Cont invokeRead socketRead namedRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                      UnaryHistory exactRead ∧ UnaryHistory invokeRead ∧
                                        UnaryHistory socketRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryB unaryE unaryI unaryU unaryS _unaryH _unaryC _unaryP _unaryN
    exactRoute invokeRoute socketRoute namedRoute pkgP pkgN
  have exactUnary : UnaryHistory exactRead :=
    unary_cont_closed unaryB unaryE exactRoute
  have invokeUnary : UnaryHistory invokeRead :=
    unary_cont_closed exactUnary unaryI invokeRoute
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed unaryU unaryS socketRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed invokeUnary socketUnary namedRoute
  constructor
  · exact
      Exists.intro
        (BEDC.Derived.SubjectReductionRouteAuditUp.mk B E I U S H C P N)
        rfl
  · constructor
    · exact {
        core := {
          carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inr source.left)))))))))))
        ledger_sound := by
          intro _row source
          exact
            ⟨source.right, exactRoute, invokeRoute, socketRoute, namedRoute, pkgP, pkgN⟩
      }
    · exact ⟨exactUnary, invokeUnary, socketUnary, namedUnary⟩

theorem SubjectReductionRouteAudit_obligation_closure [AskSetup] [PackageSetup]
    {B E I U S H C P N exactRead invokeRead socketRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory E ->
        UnaryHistory I ->
          UnaryHistory U ->
            UnaryHistory S ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont B E exactRead ->
                        Cont exactRead I invokeRead ->
                          Cont U S socketRead ->
                            Cont invokeRead socketRead namedRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row B ∨ hsame row E ∨ hsame row I ∨
                                          hsame row U ∨ hsame row S ∨ hsame row H ∨
                                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                                              hsame row exactRead ∨ hsame row invokeRead ∨
                                                hsame row socketRead ∨ hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont B E exactRead ∧
                                          Cont exactRead I invokeRead ∧ Cont U S socketRead ∧
                                            Cont invokeRead socketRead namedRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    (∃ packet : BEDC.Derived.SubjectReductionRouteAuditUp,
                                      packet =
                                        BEDC.Derived.SubjectReductionRouteAuditUp.mk
                                          B E I U S H C P N) ∧
                                      UnaryHistory exactRead ∧ UnaryHistory invokeRead ∧
                                        UnaryHistory socketRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryB unaryE unaryI unaryU unaryS _unaryH _unaryC _unaryP _unaryN
    exactRoute invokeRoute socketRoute namedRoute pkgP pkgN
  have exactUnary : UnaryHistory exactRead :=
    unary_cont_closed unaryB unaryE exactRoute
  have invokeUnary : UnaryHistory invokeRead :=
    unary_cont_closed exactUnary unaryI invokeRoute
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed unaryU unaryS socketRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed invokeUnary socketUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row E ∨ hsame row I ∨ hsame row U ∨ hsame row S ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row exactRead ∨ hsame row invokeRead ∨ hsame row socketRead ∨
                  hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B E exactRead ∧ Cont exactRead I invokeRead ∧
              Cont U S socketRead ∧ Cont invokeRead socketRead namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, exactRoute, invokeRoute, socketRoute, namedRoute, pkgP, pkgN⟩
  }
  exact
    ⟨cert,
      Exists.intro
        (BEDC.Derived.SubjectReductionRouteAuditUp.mk B E I U S H C P N)
        rfl,
      exactUnary, invokeUnary, socketUnary, namedUnary⟩

end BEDC.Derived.SubjectReductionRouteAuditUp
