import BEDC.Derived.MaxRateReadGateUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MaxRateReadGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MaxRateReadGateNameCertObligations
    {M R S F L H Q C P N rateRead symmetryRead publicRead : BHist} :
    UnaryHistory M →
      UnaryHistory R →
        UnaryHistory S →
          UnaryHistory F →
            UnaryHistory L →
              Cont M R rateRead →
                Cont rateRead S symmetryRead →
                  Cont symmetryRead F publicRead →
                    hsame H Q →
                      hsame P N →
                        SemanticNameCert
                              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row M ∨ hsame row R ∨ hsame row S ∨ hsame row F ∨
                                  hsame row L ∨ hsame row H ∨ hsame row Q ∨ hsame row C ∨
                                    hsame row P ∨ hsame row N ∨ hsame row publicRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont M R rateRead ∧
                                  Cont rateRead S symmetryRead ∧
                                    Cont symmetryRead F publicRead ∧ hsame H Q ∧ hsame P N)
                              hsame ∧
                          UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryM unaryR unaryS unaryF _unaryL rateRoute symmetryRoute publicRoute sameHQ
    samePN
  have rateUnary : UnaryHistory rateRead :=
    unary_cont_closed unaryM unaryR rateRoute
  have symmetryUnary : UnaryHistory symmetryRead :=
    unary_cont_closed rateUnary unaryS symmetryRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed symmetryUnary unaryF publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row S ∨ hsame row F ∨ hsame row L ∨
              hsame row H ∨ hsame row Q ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M R rateRead ∧ Cont rateRead S symmetryRead ∧
              Cont symmetryRead F publicRead ∧ hsame H Q ∧ hsame P N)
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rateRoute, symmetryRoute, publicRoute, sameHQ, samePN⟩
  }
  exact ⟨cert, publicUnary⟩

theorem MaxRateReadGateCarrier_downstream_consumer_boundary [AskSetup] [PackageSetup]
    {M R S F L H Q C P N symmetryRead refusalRead lockedRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory F ∧
      UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory Q ∧ UnaryHistory C ∧
        UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg →
      Cont R S symmetryRead →
        Cont symmetryRead F refusalRead →
          Cont refusalRead L lockedRead →
            Cont lockedRead C publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row R ∨ hsame row S ∨ hsame row F ∨
                        hsame row L ∨ hsame row H ∨ hsame row Q ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont R S symmetryRead ∧
                        Cont symmetryRead F refusalRead ∧ Cont refusalRead L lockedRead ∧
                          Cont lockedRead C publicRead ∧ PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory symmetryRead ∧ UnaryHistory refusalRead ∧
                    UnaryHistory lockedRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: MaxRateReadGateUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier symmetryRoute refusalRoute lockRoute publicRoute publicPkg
  obtain ⟨_mUnary, rUnary, sUnary, fUnary, lUnary, _hUnary, _qUnary, cUnary,
    _pUnary, _nUnary, _pPkg, _nPkg⟩ := carrier
  have symmetryUnary : UnaryHistory symmetryRead :=
    unary_cont_closed rUnary sUnary symmetryRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed symmetryUnary fUnary refusalRoute
  have lockedUnary : UnaryHistory lockedRead :=
    unary_cont_closed refusalUnary lUnary lockRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed lockedUnary cUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row S ∨ hsame row F ∨ hsame row L ∨
              hsame row H ∨ hsame row Q ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R S symmetryRead ∧ Cont symmetryRead F refusalRead ∧
              Cont refusalRead L lockedRead ∧ Cont lockedRead C publicRead ∧
                PkgSig bundle publicRead pkg)
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
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, symmetryRoute, refusalRoute, lockRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, symmetryUnary, refusalUnary, lockedUnary, publicUnary⟩

theorem MaxRateReadGateCarrier_cross_hist_causal_rate_handoff [AskSetup] [PackageSetup]
    {M R S F L H Q C P N symmetryRead refusalRead lockedRead publicRead handoffRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory F ∧
      UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory Q ∧ UnaryHistory C ∧
        UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg →
      Cont R S symmetryRead →
        Cont symmetryRead F refusalRead →
          Cont refusalRead L lockedRead →
            Cont lockedRead C publicRead →
              Cont publicRead N handoffRead →
                PkgSig bundle publicRead pkg →
                  PkgSig bundle handoffRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row R ∨ hsame row S ∨ hsame row F ∨
                            hsame row L ∨ hsame row H ∨ hsame row Q ∨ hsame row C ∨
                              hsame row P ∨ hsame row N ∨ hsame row publicRead ∨
                                hsame row handoffRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont R S symmetryRead ∧
                            Cont symmetryRead F refusalRead ∧
                              Cont refusalRead L lockedRead ∧
                                Cont lockedRead C publicRead ∧
                                  Cont publicRead N handoffRead ∧
                                    PkgSig bundle handoffRead pkg)
                        hsame ∧
                      UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: MaxRateReadGateUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier symmetryRoute refusalRoute lockRoute publicRoute handoffRoute _publicPkg
    handoffPkg
  obtain ⟨_mUnary, rUnary, sUnary, fUnary, lUnary, _hUnary, _qUnary, cUnary,
    _pUnary, nUnary, _pPkg, _nPkg⟩ := carrier
  have symmetryUnary : UnaryHistory symmetryRead :=
    unary_cont_closed rUnary sUnary symmetryRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed symmetryUnary fUnary refusalRoute
  have lockedUnary : UnaryHistory lockedRead :=
    unary_cont_closed refusalUnary lUnary lockRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed lockedUnary cUnary publicRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed publicUnary nUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row S ∨ hsame row F ∨ hsame row L ∨
              hsame row H ∨ hsame row Q ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R S symmetryRead ∧ Cont symmetryRead F refusalRead ∧
              Cont refusalRead L lockedRead ∧ Cont lockedRead C publicRead ∧
                Cont publicRead N handoffRead ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead
        ⟨hsame_refl handoffRead, handoffUnary⟩
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
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, symmetryRoute, refusalRoute, lockRoute, publicRoute,
          handoffRoute, handoffPkg⟩
  }
  exact ⟨cert, handoffUnary⟩

inductive MaxRateReadGateRowSource (M R S F L H Q C P N : BHist) :
    BHist → Prop where
  | multiHist : MaxRateReadGateRowSource M R S F L H Q C P N M
  | rate : MaxRateReadGateRowSource M R S F L H Q C P N R
  | symmetry : MaxRateReadGateRowSource M R S F L H Q C P N S
  | refusal : MaxRateReadGateRowSource M R S F L H Q C P N F
  | lock : MaxRateReadGateRowSource M R S F L H Q C P N L
  | transport : MaxRateReadGateRowSource M R S F L H Q C P N H
  | probe : MaxRateReadGateRowSource M R S F L H Q C P N Q
  | continuation : MaxRateReadGateRowSource M R S F L H Q C P N C
  | provenance : MaxRateReadGateRowSource M R S F L H Q C P N P
  | localName : MaxRateReadGateRowSource M R S F L H Q C P N N

def MaxRateReadGateCarrier [AskSetup] [PackageSetup]
    (M R S F L H Q C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame
  MaxRateReadGateRowSource M R S F L H Q C P N M ∧
    MaxRateReadGateRowSource M R S F L H Q C P N R ∧
      Cont S F L ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem MaxRateReadGateCarrier_namecert_package [AskSetup] [PackageSetup]
    {M R S F L H Q C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MaxRateReadGateCarrier M R S F L H Q C P N bundle pkg →
      NameCert (MaxRateReadGateRowSource M R S F L H Q C P N) hsame ∧
        Cont S F L ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame NameCert
  intro carrier
  obtain ⟨sourceM, _sourceR, route, pPkg, nPkg⟩ := carrier
  have cert : NameCert (MaxRateReadGateRowSource M R S F L H Q C P N) hsame := {
    carrier_inhabited := Exists.intro M sourceM
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
      intro row other sameRows source
      cases sameRows
      exact source
  }
  exact ⟨cert, route, pPkg, nPkg⟩

theorem MaxRateReadGateCarrier_namecert_obligation_coverage [AskSetup] [PackageSetup]
    {M R S F L H Q C P N rateRead symmetryRead refusalRead lockedRead publicRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory F ∧
      UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory Q ∧ UnaryHistory C ∧
        UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ->
      Cont M R rateRead ->
        Cont rateRead S symmetryRead ->
          Cont R S symmetryRead ->
            Cont symmetryRead F refusalRead ->
              Cont refusalRead L lockedRead ->
                Cont lockedRead C publicRead ->
                  Cont publicRead N handoffRead ->
                    hsame H Q ->
                      hsame P N ->
                        PkgSig bundle publicRead pkg ->
                          PkgSig bundle handoffRead pkg ->
                            SemanticNameCert
                                (fun row : BHist =>
                                  hsame row handoffRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row M ∨ hsame row R ∨ hsame row S ∨
                                    hsame row F ∨ hsame row L ∨ hsame row H ∨
                                      hsame row Q ∨ hsame row C ∨ hsame row P ∨
                                        hsame row N ∨ hsame row publicRead ∨
                                          hsame row handoffRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont R S symmetryRead ∧
                                    Cont symmetryRead F refusalRead ∧
                                      Cont refusalRead L lockedRead ∧
                                        Cont lockedRead C publicRead ∧
                                          Cont publicRead N handoffRead ∧
                                            PkgSig bundle handoffRead pkg)
                                hsame ∧
                              UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: MaxRateReadGateUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier rateRoute rateSymmetryRoute symmetryRoute refusalRoute lockRoute publicRoute
    handoffRoute sameHQ samePN publicPkg handoffPkg
  have rateSurface :=
    MaxRateReadGateNameCertObligations carrier.left carrier.right.left carrier.right.right.left
      carrier.right.right.right.left carrier.right.right.right.right.left rateRoute
      rateSymmetryRoute (C := C) refusalRoute sameHQ samePN
  have consumerSurface :=
    MaxRateReadGateCarrier_downstream_consumer_boundary carrier symmetryRoute refusalRoute
      lockRoute publicRoute publicPkg
  have handoffSurface :=
    MaxRateReadGateCarrier_cross_hist_causal_rate_handoff carrier symmetryRoute refusalRoute
      lockRoute publicRoute handoffRoute publicPkg handoffPkg
  have packageRows :
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg :=
    ⟨carrier.right.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right⟩
  obtain ⟨_rateCert, _refusalUnary⟩ := rateSurface
  obtain ⟨_consumerCert, _symmetryUnary, _lockedRefusalUnary, _lockedUnary, _publicUnary⟩ :=
    consumerSurface
  obtain ⟨_handoffCert, handoffUnary⟩ := handoffSurface
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row S ∨ hsame row F ∨ hsame row L ∨
              hsame row H ∨ hsame row Q ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R S symmetryRead ∧ Cont symmetryRead F refusalRead ∧
              Cont refusalRead L lockedRead ∧ Cont lockedRead C publicRead ∧
                Cont publicRead N handoffRead ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead
        ⟨hsame_refl handoffRead, handoffUnary⟩
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
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, symmetryRoute, refusalRoute, lockRoute, publicRoute,
          handoffRoute, handoffPkg⟩
  }
  exact ⟨cert, handoffUnary⟩

end BEDC.Derived.MaxRateReadGateUp
