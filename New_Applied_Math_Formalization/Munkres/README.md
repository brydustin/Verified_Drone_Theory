# Vendored Munkres Topology

This directory contains local copies of the four main chapter theories from:

- `/home/dusty/Desktop/Academic/Isabelle_Stuff/Topology/isa_top_autoform1/tst/i/`

Copied files:

- [Top1_Ch2.thy](/home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology/Top1_Ch2.thy)
- [Top1_Ch3.thy](/home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology/Top1_Ch3.thy)
- [Top1_Ch4.thy](/home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology/Top1_Ch4.thy)
- [Top1_Ch5_8.thy](/home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology/Top1_Ch5_8.thy)

Wrapper session:

- [ROOT](/home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology/ROOT:1)
- [Munkres_Topology.thy](/home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology/Munkres_Topology.thy:1)

Notes:

- The upstream `tst/ROOT` split these into `Top0` and `Top1`.
- Here they are vendored into a single local session `Munkres_Topology_Local`.
- A search for actual proof commands of the form `sorry` in these four files returned no matches.

Immediately relevant result for the nonemptiness work:

- `Theorem_48_2` in [Top1_Ch5_8.thy](/home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology/Top1_Ch5_8.thy:23453)

That theorem gives the Baire-category result in this development's own topology language.
