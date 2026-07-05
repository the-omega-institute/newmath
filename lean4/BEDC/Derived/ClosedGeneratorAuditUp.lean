import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedGeneratorAuditCarrier [AskSetup] [PackageSetup]
    (T K R S A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory T ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory S ∧
    UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle N pkg

theorem ClosedGeneratorAuditCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {T K R S A H C P N replayRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedGeneratorAuditCarrier T K R S A H C P N bundle pkg →
      Cont T S replayRead →
        Cont replayRead A auditRead →
          PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row N ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row T ∨ hsame row K ∨ hsame row R ∨ hsame row S ∨
                    hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row replayRead ∨ hsame row auditRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont T S replayRead ∧
                    Cont replayRead A auditRead ∧ PkgSig bundle N pkg)
                hsame ∧ UnaryHistory replayRead ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: ClosedGeneratorAuditCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier replayRoute auditRoute namePkg
  obtain ⟨tUnary, _kUnary, _rUnary, sUnary, aUnary, _hUnary, _cUnary, _pUnary,
    nUnary, _carrierNamePkg⟩ := carrier
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed tUnary sUnary replayRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed replayUnary aUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row K ∨ hsame row R ∨ hsame row S ∨ hsame row A ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row replayRead ∨ hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T S replayRead ∧ Cont replayRead A auditRead ∧
              PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, replayRoute, auditRoute, namePkg⟩
  }
  exact ⟨cert, replayUnary, auditUnary⟩

theorem ClosedGeneratorAuditCarrier_nonescape [AskSetup] [PackageSetup]
    {T K R S A H C P N replayRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedGeneratorAuditCarrier T K R S A H C P N bundle pkg →
      Cont T S replayRead →
        Cont replayRead A auditRead →
          PkgSig bundle N pkg →
            SemanticNameCert
              (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row T ∨ hsame row K ∨ hsame row R ∨ hsame row S ∨
                  hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                    hsame row N ∨ hsame row replayRead ∨ hsame row auditRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont T S replayRead ∧
                  Cont replayRead A auditRead ∧ PkgSig bundle N pkg)
              hsame ∧ UnaryHistory replayRead ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: ClosedGeneratorAuditCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier replayRoute auditRoute namePkg
  obtain ⟨tUnary, _kUnary, _rUnary, sUnary, aUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _carrierNamePkg⟩ := carrier
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed tUnary sUnary replayRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed replayUnary aUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row K ∨ hsame row R ∨ hsame row S ∨ hsame row A ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row replayRead ∨ hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T S replayRead ∧ Cont replayRead A auditRead ∧
              PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
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
                          (Or.inr sourceRow.left)))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, replayRoute, auditRoute, namePkg⟩
  }
  exact ⟨cert, replayUnary, auditUnary⟩

theorem ClosedGeneratorAuditCarrier_refusal_replay_exactness [AskSetup] [PackageSetup]
    {T K R S A H C P N replayRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedGeneratorAuditCarrier T K R S A H C P N bundle pkg →
      Cont T S replayRead →
        Cont replayRead A auditRead →
          PkgSig bundle N pkg →
            SemanticNameCert
              (fun row : BHist => hsame row A ∨ hsame row auditRead)
              (fun row : BHist =>
                hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row auditRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont replayRead A auditRead ∧ PkgSig bundle N pkg)
              hsame ∧ UnaryHistory A ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: ClosedGeneratorAuditCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier replayRoute auditRoute namePkg
  obtain ⟨tUnary, _kUnary, _rUnary, sUnary, aUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _carrierNamePkg⟩ := carrier
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed tUnary sUnary replayRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed replayUnary aUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row A ∨ hsame row auditRead)
          (fun row : BHist =>
            hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
              hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont replayRead A auditRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro A (Or.inl (hsame_refl A))
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
        intro _row _other sameRows sourceRow
        cases sourceRow with
        | inl auditSource =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) auditSource)
        | inr auditReadSource =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) auditReadSource)
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow with
      | inl auditSource =>
          exact Or.inl auditSource
      | inr auditReadSource =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr auditReadSource))))
    ledger_sound := by
      intro _row sourceRow
      cases sourceRow with
      | inl auditSource =>
          exact ⟨unary_transport_symm aUnary auditSource, auditRoute, namePkg⟩
      | inr auditReadSource =>
          exact ⟨unary_transport_symm auditUnary auditReadSource, auditRoute, namePkg⟩
  }
  exact ⟨cert, aUnary, auditUnary⟩

theorem ClosedGeneratorAuditCarrier_kernel_replay_induction [AskSetup] [PackageSetup]
    {T K R S A H C P N replayRead auditRead kernelRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedGeneratorAuditCarrier T K R S A H C P N bundle pkg →
      Cont K R kernelRead →
        Cont T S replayRead →
          Cont replayRead A auditRead →
            Cont kernelRead auditRead publicRead →
              PkgSig bundle N pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row R ∨ hsame row S ∨ hsame row A ∨
                        hsame row replayRead ∨ hsame row auditRead ∨
                          hsame row kernelRead ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont K R kernelRead ∧ Cont T S replayRead ∧
                        Cont replayRead A auditRead ∧ Cont kernelRead auditRead publicRead ∧
                          PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory kernelRead ∧ UnaryHistory replayRead ∧
                    UnaryHistory auditRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: ClosedGeneratorAuditCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier kernelRoute replayRoute auditRoute publicRoute namePkg
  obtain ⟨tUnary, kUnary, rUnary, sUnary, aUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _carrierNamePkg⟩ := carrier
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed kUnary rUnary kernelRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed tUnary sUnary replayRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed replayUnary aUnary auditRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed kernelUnary auditUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row R ∨ hsame row S ∨ hsame row A ∨
              hsame row replayRead ∨ hsame row auditRead ∨ hsame row kernelRead ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K R kernelRead ∧ Cont T S replayRead ∧
              Cont replayRead A auditRead ∧ Cont kernelRead auditRead publicRead ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, kernelRoute, replayRoute, auditRoute, publicRoute, namePkg⟩
  }
  exact ⟨cert, kernelUnary, replayUnary, auditUnary, publicUnary⟩

theorem ClosedGeneratorAuditCarrier_obligation_boundary [AskSetup] [PackageSetup]
    {T K R S A H C P N replayRead auditRead kernelRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedGeneratorAuditCarrier T K R S A H C P N bundle pkg ->
      Cont K R kernelRead ->
        Cont T S replayRead ->
          Cont replayRead A auditRead ->
            Cont kernelRead auditRead publicRead ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row T ∨ hsame row K ∨ hsame row R ∨ hsame row S ∨
                        hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row replayRead ∨ hsame row auditRead ∨
                            hsame row kernelRead ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont K R kernelRead ∧ Cont T S replayRead ∧
                        Cont replayRead A auditRead ∧ Cont kernelRead auditRead publicRead ∧
                          PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory T ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory S ∧
                    UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
                      UnaryHistory N ∧ UnaryHistory kernelRead ∧ UnaryHistory replayRead ∧
                        UnaryHistory auditRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: ClosedGeneratorAuditCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier kernelRoute replayRoute auditRoute publicRoute namePkg
  obtain ⟨tUnary, kUnary, rUnary, sUnary, aUnary, hUnary, cUnary, pUnary, nUnary,
    _carrierNamePkg⟩ := carrier
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed kUnary rUnary kernelRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed tUnary sUnary replayRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed replayUnary aUnary auditRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed kernelUnary auditUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row K ∨ hsame row R ∨ hsame row S ∨ hsame row A ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row replayRead ∨ hsame row auditRead ∨ hsame row kernelRead ∨
                  hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K R kernelRead ∧ Cont T S replayRead ∧
              Cont replayRead A auditRead ∧ Cont kernelRead auditRead publicRead ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, kernelRoute, replayRoute, auditRoute, publicRoute, namePkg⟩
  }
  exact
    ⟨cert, tUnary, kUnary, rUnary, sUnary, aUnary, hUnary, cUnary, pUnary, nUnary,
      kernelUnary, replayUnary, auditUnary, publicUnary⟩

end BEDC.Derived
