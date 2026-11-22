/-
  INFO v1.0.0 — Pure Information & Coding ABI Schema Compiler
  ===========================================================
  Consumes domain-free `../FLOW/{core,sdk}` (`Flow.Schema`) to configure the 256-slot
  `16,384B` `infoArenaSchema` and emit zero-`memcpy` `build/info_schema_abi.h`.
  ZERO local definitions of theorems, lemmas, or axioms.
-/
import Flow.Schema

namespace Info

open Flow.Schema

def hdrLayout : CellLayout64 :=
  CellLayout64.packed64 "hdr" "InfoHeader64" "hdr"
    [ ("magic", .u32, 1)
    , ("version", .u32, 1)
    , ("total_cells", .u32, 1)
    , ("codec_flags", .u32, 1)
    , ("orig_size", .u64, 1)
    , ("compressed_size", .u64, 1)
    , ("payload_hash", .u64, 1)
    , ("merkle_root", .u64, 1)
    , ("pad", .u64, 2)
    ]

def codecStatsLayout : CellLayout64 :=
  CellLayout64.packed64 "codec_stats" "InfoCodecStats64" "codec_stats"
    [ ("orig_bits", .u64, 1)
    , ("compressed_bits", .u64, 1)
    , ("alg_hits", .u64, 1)
    , ("match_hits", .u64, 1)
    , ("max_surprise_q12", .u64, 1)
    , ("spike_offset", .u64, 1)
    , ("bpb_q12", .u64, 1)
    , ("roundtrip_ok", .u64, 1)
    ]

def ctwMetaLayout : CellLayout64 :=
  CellLayout64.packed64 "ctw_meta" "InfoCtwMeta64" "ctw_meta"
    [ ("trials", .u64, 1)
    , ("kt_bits_q12", .u64, 1)
    , ("ctw_bits_q12", .u64, 1)
    , ("switch_bits_q12", .u64, 1)
    , ("mixer_bits_q12", .u64, 1)
    , ("entropy_q12", .u64, 1)
    , ("depth", .u32, 1)
    , ("switches", .u32, 1)
    , ("merkle", .u64, 1)
    ]

def sepMetaLayout : CellLayout64 :=
  CellLayout64.packed64 "sep_meta" "InfoSepMeta64" "sep_meta"
    [ ("stream_bytes", .u64, 1)
    , ("pure_ctx_bits", .u64, 1)
    , ("full_induct_bits", .u64, 1)
    , ("alg_hits", .u64, 1)
    , ("roundtrip_ok", .u32, 1)
    , ("law_kind", .u32, 1)
    , ("seed", .u64, 1)
    , ("merkle", .u64, 1)
    , ("pad", .u64, 1)
    ]

def delsarteMetaLayout : CellLayout64 :=
  CellLayout64.packed64 "delsarte_meta" "InfoDelsarteMeta64" "delsarte_meta"
    [ ("n", .u32, 1)
    , ("d", .u32, 1)
    , ("searu_code_size", .u64, 1)
    , ("singleton_ub", .u64, 1)
    , ("hamming_ub", .u64, 1)
    , ("delsarte_ub_num", .u64, 1)
    , ("delsarte_ub_den", .u64, 1)
    , ("dual_verified", .u32, 1)
    , ("tight", .u32, 1)
    , ("merkle", .u64, 1)
    ]

def causalMetaLayout : CellLayout64 :=
  CellLayout64.packed64 "causal_meta" "InfoCausalMeta64" "causal_meta"
    [ ("env1_x", .u64, 1)
    , ("env1_y", .u64, 1)
    , ("len_xy_q12", .u64, 1)
    , ("len_yx_q12", .u64, 1)
    , ("bp_low_num", .i64, 1)
    , ("bp_high_num", .i64, 1)
    , ("bp_den", .u64, 1)
    , ("direction_ok", .u32, 1)
    , ("bp_sound", .u32, 1)
    ]

def infoArenaSchema : ArenaSpec where
  cPrefix         := "info_schema"
  headerGuard     := "INFO_SCHEMA_ABI_H"
  totalCells      := 256
  cCellUnionName  := "InfoCell64"
  cArenaMapName   := "InfoArenaMap"
  cArenaUnionName := "InfoArena"
  regions :=
    [ { name := "hdr"
      , baseSlot := 0
      , count := 1
      , cSlotMacro := "INFO_SLOT_HDR"
      , mapDecl := "InfoHeader64 hdr;"
      }
    , { name := "codec_stats"
      , baseSlot := 1
      , count := 1
      , cSlotMacro := "INFO_SLOT_CODEC_STATS"
      , mapDecl := "InfoCodecStats64 codec_stats;"
      }
    , { name := "ctw_meta"
      , baseSlot := 2
      , count := 4
      , cSlotMacro := "INFO_SLOT_CTW_META_BASE"
      , cCountMacro := "INFO_COUNT_CTW_META"
      , mapDecl := "InfoCtwMeta64 ctw_meta[INFO_COUNT_CTW_META];"
      }
    , { name := "sep_meta"
      , baseSlot := 6
      , count := 4
      , cSlotMacro := "INFO_SLOT_SEP_META_BASE"
      , cCountMacro := "INFO_COUNT_SEP_META"
      , mapDecl := "InfoSepMeta64 sep_meta[INFO_COUNT_SEP_META];"
      }
    , { name := "delsarte_meta"
      , baseSlot := 10
      , count := 16
      , cSlotMacro := "INFO_SLOT_DELSARTE_META_BASE"
      , cCountMacro := "INFO_COUNT_DELSARTE_META"
      , mapDecl := "InfoDelsarteMeta64 delsarte_meta[INFO_COUNT_DELSARTE_META];"
      }
    , { name := "causal_meta"
      , baseSlot := 26
      , count := 8
      , cSlotMacro := "INFO_SLOT_CAUSAL_META_BASE"
      , cCountMacro := "INFO_COUNT_CAUSAL_META"
      , mapDecl := "InfoCausalMeta64 causal_meta[INFO_COUNT_CAUSAL_META];"
      }
    , { name := "aux"
      , baseSlot := 34
      , count := 222
      , cSlotMacro := "INFO_SLOT_AUX_BASE"
      , cCountMacro := "INFO_MAX_AUX"
      , mapDecl := "uint64_t aux[INFO_MAX_AUX][8];"
      }
    ]
  layouts :=
    [ hdrLayout
    , codecStatsLayout
    , ctwMetaLayout
    , sepMetaLayout
    , delsarteMetaLayout
    , causalMetaLayout
    ]

def emitSchemaOnly (outPath : System.FilePath) : IO Unit := do
  let ok ← ArenaSpec.emitC17HeaderChecked outPath infoArenaSchema
  if !ok then
    throw <| IO.userError s!"Info: ArenaSpec verification failed emitting {outPath}"

end Info

def main (args : List String) : IO Unit := do
  match args with
  | ["emit-schema", outPath] => Info.emitSchemaOnly outPath
  | _ => Info.emitSchemaOnly "build/info_schema_abi.h"
