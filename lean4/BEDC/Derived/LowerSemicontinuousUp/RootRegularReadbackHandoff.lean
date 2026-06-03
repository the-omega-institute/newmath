import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootRegularReadbackHandoff [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead locatedRead transportRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] →
      UnaryHistory W → UnaryHistory R → UnaryHistory E → UnaryHistory O → UnaryHistory H →
        UnaryHistory C → Cont W R windowRead → Cont windowRead E epigraphRead →
          Cont epigraphRead O locatedRead → Cont locatedRead H transportRead →
            Cont transportRead C handoffRead → PkgSig bundle P pkg →
              PkgSig bundle N pkg → SemanticNameCert
                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
                    hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                      hsame row handoffRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont W R windowRead ∧
                    Cont windowRead E epigraphRead ∧ Cont epigraphRead O locatedRead ∧
                      Cont locatedRead H transportRead ∧ Cont transportRead C handoffRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame ∧ UnaryHistory windowRead ∧ UnaryHistory epigraphRead ∧
                  UnaryHistory locatedRead ∧ UnaryHistory transportRead ∧
                    UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro fields wUnary rUnary eUnary oUnary hUnary cUnary windowRoute epigraphRoute
    locatedRoute transportRoute handoffRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed locatedUnary hUnary transportRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed transportUnary cUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E epigraphRead ∧
              Cont epigraphRead O locatedRead ∧ Cont locatedRead H transportRead ∧
                Cont transportRead C handoffRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
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
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, epigraphRoute, locatedRoute, transportRoute,
          handoffRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, windowUnary, epigraphUnary, locatedUnary, transportUnary, handoffUnary⟩

theorem LowerSemicontinuousKernelSource_obligations [AskSetup] [PackageSetup]
    {X F E W R O H C P N scheduleRead readbackRead epigraphRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X -> UnaryHistory W -> UnaryHistory R -> UnaryHistory E ->
      Cont X W scheduleRead -> Cont scheduleRead R readbackRead ->
        Cont readbackRead E epigraphRead -> PkgSig bundle P pkg ->
          PkgSig bundle N pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row epigraphRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row F ∨ hsame row E ∨ hsame row W ∨
                  hsame row R ∨ hsame row O ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N ∨ hsame row scheduleRead ∨
                      hsame row readbackRead ∨ hsame row epigraphRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont X W scheduleRead ∧
                  Cont scheduleRead R readbackRead ∧ Cont readbackRead E epigraphRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧ UnaryHistory scheduleRead ∧ UnaryHistory readbackRead ∧
                UnaryHistory epigraphRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro xUnary wUnary rUnary eUnary scheduleRoute readbackRoute epigraphRoute
    provenancePkg namePkg
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed xUnary wUnary scheduleRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed scheduleUnary rUnary readbackRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed readbackUnary eUnary epigraphRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row epigraphRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row F ∨ hsame row E ∨ hsame row W ∨
            hsame row R ∨ hsame row O ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row scheduleRead ∨
                hsame row readbackRead ∨ hsame row epigraphRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont X W scheduleRead ∧
            Cont scheduleRead R readbackRead ∧ Cont readbackRead E epigraphRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro epigraphRead ⟨hsame_refl epigraphRead, epigraphUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, scheduleRoute, readbackRoute, epigraphRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, scheduleUnary, readbackUnary, epigraphUnary⟩

theorem LowerSemicontinuousRegularReadback_transport [AskSetup] [PackageSetup]
    {W R E O H C P N W' R' E' readback readback' located located' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W -> UnaryHistory R -> UnaryHistory E -> UnaryHistory O ->
      hsame W W' -> hsame R R' -> hsame E E' -> Cont W R readback ->
        Cont W' R' readback' -> Cont readback E located ->
          Cont readback' E' located' -> PkgSig bundle P pkg -> PkgSig bundle N pkg ->
            hsame readback readback' ∧ hsame located located' ∧
              SemanticNameCert
                (fun row : BHist => hsame row located ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
                    hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                      hsame row readback ∨ hsame row located)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont W R readback ∧ Cont readback E located ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro wUnary rUnary eUnary _oUnary sameW sameR sameE readbackRoute readbackRoute'
    locatedRoute locatedRoute' provenancePkg namePkg
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed wUnary rUnary readbackRoute
  have locatedUnary : UnaryHistory located :=
    unary_cont_closed readbackUnary eUnary locatedRoute
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameW sameR readbackRoute readbackRoute'
  have sameLocated : hsame located located' :=
    cont_respects_hsame sameReadback sameE locatedRoute locatedRoute'
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row located ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
              hsame row readback ∨ hsame row located)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont W R readback ∧ Cont readback E located ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro located ⟨hsame_refl located, locatedUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, readbackRoute, locatedRoute, provenancePkg, namePkg⟩
  }
  exact ⟨sameReadback, sameLocated, cert⟩

end BEDC.Derived.LowerSemicontinuousUp
