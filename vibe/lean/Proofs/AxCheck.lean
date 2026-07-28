/-
SPDX-FileCopyrightText: 2026 Saimono / Nova-Violet Role
SPDX-License-Identifier: AGPL-3.0-or-later OR EUPL-1.2
-/
import Proofs.Compressor
open Compressor
#print axioms shipped_tag_kind_confusion
#print axioms summary_tag_replays_as_pin
#print axioms fixed_blocks_kind_confusion
#print axioms fixed_accepts_honest
#print axioms rescue_can_emit_orphan
#print axioms known_ids_span_dropped_messages
#print axioms dropOrphansAux_orphanFree
#print axioms orphanFreeAux_system_prefix
#print axioms mem_take_sysPrefixLen
#print axioms fixed_validate_orphanFree
#print axioms fixed_validate_keeps_content
#print axioms overskip_moves_match_end
#print axioms empty_chain_never_matches
#print axioms underskip_kills_the_match
#print axioms walk_stops_at_first_unpinned
#print axioms chainStart_walks_pins
