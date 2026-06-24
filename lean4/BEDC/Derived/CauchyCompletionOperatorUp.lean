import BEDC.Derived.CauchyCompletionOperatorUp.TasteGate
import BEDC.Derived.CauchyCompletionOperatorUp.SeparatedLimitFactorization
import BEDC.Derived.CauchyCompletionOperatorUp.LedgerNonescape
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionOperatorPacket [AskSetup] [PackageSetup]
    (metric boundary uniform windows readback dyadic separated realSeal transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  hsame localName realSeal ∧
    Cont metric uniform boundary ∧
      Cont boundary windows readback ∧
        Cont readback dyadic separated ∧
          Cont separated realSeal transport ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem CauchyCompletionOperator_namecert_obligation_surface [AskSetup] [PackageSetup]
    {metric boundary uniform windows readback dyadic separated realSeal transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorPacket metric boundary uniform windows readback dyadic separated
        realSeal transport replay provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              CauchyCompletionOperatorPacket metric boundary uniform windows readback dyadic
                separated realSeal transport replay provenance localName bundle pkg)
          (fun row : BHist =>
            hsame row metric ∨ hsame row boundary ∨ hsame row uniform ∨
              hsame row windows ∨ hsame row readback ∨ hsame row dyadic ∨
                hsame row separated ∨ hsame row realSeal ∨ hsame row localName)
          (fun row : BHist =>
            hsame row localName ∧ Cont metric uniform boundary ∧
              Cont boundary windows readback ∧ Cont readback dyadic separated ∧
                Cont separated realSeal transport ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet
  obtain
    ⟨localRealSeal, metricUniformBoundary, boundaryWindowsReadback,
      readbackDyadicSeparated, separatedRealSealTransport, provenancePackage,
      localPackage⟩ := packet
  have packetAtLocalName :
      hsame localName localName ∧
        CauchyCompletionOperatorPacket metric boundary uniform windows readback dyadic
          separated realSeal transport replay provenance localName bundle pkg := by
    exact
      ⟨hsame_refl localName, localRealSeal, metricUniformBoundary,
        boundaryWindowsReadback, readbackDyadicSeparated, separatedRealSealTransport,
        provenancePackage, localPackage⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro localName packetAtLocalName
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
          ⟨hsame_trans (hsame_symm sameRows) source.left, localRealSeal,
            metricUniformBoundary, boundaryWindowsReadback, readbackDyadicSeparated,
            separatedRealSealTransport, provenancePackage, localPackage⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, metricUniformBoundary, boundaryWindowsReadback,
          readbackDyadicSeparated, separatedRealSealTransport, provenancePackage,
          localPackage⟩
  }

theorem CauchyCompletionOperatorRealSealNonescape [AskSetup] [PackageSetup]
    {M B U S R D Q E H C P N boundaryRead finiteWindow separatedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorLedgerPacket M B U S R D Q E H C P N bundle pkg ->
      Cont M U boundaryRead ->
        Cont B S finiteWindow ->
          Cont D Q separatedRead ->
            Cont separatedRead E sealRead ->
              PkgSig bundle sealRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row B ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                        hsame row Q ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row finiteWindow ∨
                            hsame row separatedRead ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont B S finiteWindow ∧
                        Cont D Q separatedRead ∧ Cont separatedRead E sealRead ∧
                          PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory boundaryRead ∧ UnaryHistory finiteWindow ∧
                    UnaryHistory separatedRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet metricUniformBoundary boundaryWindow dyadicSeparated separatedSeal sealPkg
  obtain ⟨metricUnary, boundaryUnary, uniformUnary, streamUnary, _regularUnary,
    dyadicUnary, separatedUnary, realSealUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _nameUnary, _streamRegularDyadic, _dyadicSeparatedReal,
    _provenancePkg, _namePkg⟩ := packet
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed metricUnary uniformUnary metricUniformBoundary
  have finiteUnary : UnaryHistory finiteWindow :=
    unary_cont_closed boundaryUnary streamUnary boundaryWindow
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed dyadicUnary separatedUnary dyadicSeparated
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed separatedReadUnary realSealUnary separatedSeal
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row Q ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row finiteWindow ∨ hsame row separatedRead ∨
                  hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B S finiteWindow ∧ Cont D Q separatedRead ∧
              Cont separatedRead E sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, boundaryWindow, dyadicSeparated, separatedSeal, sealPkg⟩
  }
  exact ⟨cert, boundaryReadUnary, finiteUnary, separatedReadUnary, sealUnary⟩

theorem CauchyCompletionOperatorObligationWindowRoute [AskSetup] [PackageSetup]
    {M B U S R D Q E H C P N boundaryRead finiteWindow separatedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorLedgerPacket M B U S R D Q E H C P N bundle pkg ->
      Cont M U boundaryRead ->
        Cont B S finiteWindow ->
          Cont D Q separatedRead ->
            Cont separatedRead E sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory M ∧ UnaryHistory U ∧ UnaryHistory B ∧ UnaryHistory S ∧
                  UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory Q ∧ UnaryHistory E ∧
                    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
                      UnaryHistory boundaryRead ∧ UnaryHistory finiteWindow ∧
                        UnaryHistory separatedRead ∧ UnaryHistory sealRead ∧
                          Cont M U boundaryRead ∧ Cont B S finiteWindow ∧
                            Cont D Q separatedRead ∧ Cont separatedRead E sealRead ∧
                              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet metricUniformBoundary boundaryWindow dyadicSeparated separatedSeal sealPkg
  obtain ⟨metricUnary, boundaryUnary, uniformUnary, streamUnary, regularUnary,
    dyadicUnary, separatedUnary, realSealUnary, transportUnary, replayUnary,
    provenanceUnary, nameUnary, _streamRegularDyadic, _dyadicSeparatedReal,
    _provenancePkg, _namePkg⟩ := packet
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed metricUnary uniformUnary metricUniformBoundary
  have finiteUnary : UnaryHistory finiteWindow :=
    unary_cont_closed boundaryUnary streamUnary boundaryWindow
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed dyadicUnary separatedUnary dyadicSeparated
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed separatedReadUnary realSealUnary separatedSeal
  exact
    ⟨metricUnary, uniformUnary, boundaryUnary, streamUnary, regularUnary, dyadicUnary,
      separatedUnary, realSealUnary, transportUnary, replayUnary, provenanceUnary, nameUnary,
      boundaryReadUnary, finiteUnary, separatedReadUnary, sealUnary, metricUniformBoundary,
      boundaryWindow, dyadicSeparated, separatedSeal, sealPkg⟩

theorem CauchyCompletionOperatorScopedObligationClosure [AskSetup] [PackageSetup]
    {M B U S R D Q E H C P N boundaryRead finiteWindow separatedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorLedgerPacket M B U S R D Q E H C P N bundle pkg ->
      Cont M U boundaryRead ->
        Cont B S finiteWindow ->
          Cont finiteWindow R D ->
            Cont D Q separatedRead ->
              Cont separatedRead E sealRead ->
                PkgSig bundle P pkg ->
                  PkgSig bundle N pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row N ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row B ∨ hsame row U ∨ hsame row S ∨
                            hsame row R ∨ hsame row D ∨ hsame row Q ∨ hsame row E ∨
                              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                                hsame row boundaryRead ∨ hsame row finiteWindow ∨
                                  hsame row separatedRead ∨ hsame row sealRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont M U boundaryRead ∧
                            Cont B S finiteWindow ∧ Cont finiteWindow R D ∧
                              Cont D Q separatedRead ∧ Cont separatedRead E sealRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                        hsame ∧
                      UnaryHistory boundaryRead ∧ UnaryHistory finiteWindow ∧
                        UnaryHistory separatedRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet metricUniformBoundary boundaryWindow finiteRegular
    dyadicSeparated separatedSeal provenancePkg namePkg
  obtain ⟨metricUnary, boundaryUnary, uniformUnary, streamUnary, regularUnary,
    dyadicUnary, separatedUnary, realSealUnary, _transportUnary, _replayUnary,
    _provenanceUnary, nameUnary, _streamRegularDyadic, _dyadicSeparatedReal,
    _provenancePkg, _namePkg⟩ := packet
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed metricUnary uniformUnary metricUniformBoundary
  have finiteUnary : UnaryHistory finiteWindow :=
    unary_cont_closed boundaryUnary streamUnary boundaryWindow
  have dyadicFromFiniteUnary : UnaryHistory D :=
    unary_cont_closed finiteUnary regularUnary finiteRegular
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed dyadicUnary separatedUnary dyadicSeparated
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed separatedReadUnary realSealUnary separatedSeal
  have sourceName :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, nameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row B ∨ hsame row U ∨ hsame row S ∨
              hsame row R ∨ hsame row D ∨ hsame row Q ∨ hsame row E ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row boundaryRead ∨ hsame row finiteWindow ∨
                    hsame row separatedRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M U boundaryRead ∧ Cont B S finiteWindow ∧
              Cont finiteWindow R D ∧ Cont D Q separatedRead ∧
                Cont separatedRead E sealRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceName
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact Or.inl sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, metricUniformBoundary, boundaryWindow, finiteRegular,
          dyadicSeparated, separatedSeal, provenancePkg, namePkg⟩
  }
  exact ⟨cert, boundaryReadUnary, finiteUnary, separatedReadUnary, sealUnary⟩

theorem CauchyCompletionOperatorPublicExport [AskSetup] [PackageSetup]
    {M B U S R D Q E H C P N boundaryRead finiteWindow separatedRead sealRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorLedgerPacket M B U S R D Q E H C P N bundle pkg →
      Cont M U boundaryRead →
        Cont B S finiteWindow →
          Cont D Q separatedRead →
            Cont separatedRead E sealRead →
              Cont sealRead N publicRead →
                PkgSig bundle publicRead pkg →
                  UnaryHistory M ∧ UnaryHistory B ∧ UnaryHistory U ∧ UnaryHistory S ∧
                    UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory Q ∧ UnaryHistory E ∧
                      UnaryHistory publicRead ∧ Cont M U boundaryRead ∧
                        Cont B S finiteWindow ∧ Cont D Q separatedRead ∧
                          Cont separatedRead E sealRead ∧ Cont sealRead N publicRead ∧
                            PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet metricUniformBoundary boundaryWindow dyadicSeparated separatedSeal
    sealPublic publicPkg
  obtain ⟨metricUnary, boundaryUnary, uniformUnary, streamUnary, _regularUnary,
    dyadicUnary, separatedUnary, realSealUnary, _transportUnary, _replayUnary,
    _provenanceUnary, nameUnary, _streamRegularDyadic, _dyadicSeparatedReal,
    _provenancePkg, _namePkg⟩ := packet
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed metricUnary uniformUnary metricUniformBoundary
  have finiteUnary : UnaryHistory finiteWindow :=
    unary_cont_closed boundaryUnary streamUnary boundaryWindow
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed dyadicUnary separatedUnary dyadicSeparated
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed separatedReadUnary realSealUnary separatedSeal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary nameUnary sealPublic
  exact
    ⟨metricUnary, boundaryUnary, uniformUnary, streamUnary, _regularUnary, dyadicUnary,
      separatedUnary, realSealUnary, publicUnary, metricUniformBoundary, boundaryWindow,
      dyadicSeparated, separatedSeal, sealPublic, publicPkg⟩

end BEDC.Derived.CauchyCompletionOperatorUp
