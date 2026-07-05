namespace UnifiedTheory.Kernel

inductive LedgerStatus where
  | open
  | closed
  | tail
  | semantic
deriving DecidableEq, Repr

end UnifiedTheory.Kernel
