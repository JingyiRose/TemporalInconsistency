import DetectInconsistency
from DetectInconsistency import One_Inconsistent_Recon

# a reconciliation with temporal inconsistency
host_tree_1 = { 'hTop': ('Top', 'm0', ('m0', 'm1'), ('m0', 'm4')),
('m0', 'm1'): ('m0', 'm1', ('m1', 'm2'), ('m1', 'm3')),
('m0', 'm4'): ('m0', 'm4', ('m4', 'm5'), ('m4', 'm6')),
('m1', 'm2'): ('m1', 'm2', None, None),
('m1', 'm3'): ('m1', 'm3', None, None),
('m4', 'm5'): ('m4', 'm5', None, None),
('m4', 'm6'): ('m4', 'm6', None, None)}

parasite_tree_1 = { 'pTop': ('Top', 'n0', ('n0', 'n1'), ('n0', 'n5')),
('n0', 'n1'): ('n0', 'n1', ('n1', 'n2'), ('n1', 'n3')),
('n1', 'n3'): ('n1', 'n3', ('n3', 'n4'), ('n3', 'n6')),
('n1', 'n2'): ('n1', 'n2', None, None),
('n3', 'n4'): ('n3', 'n4', None, None),
('n0', 'n5'): ('n0', 'n5', None, None),
('n3', 'n6'): ('n3', 'n6', None, None),}

reconciliation_1 = { ('n0', 'm1'): [('T', ('n1', 'm1'), ('n5', 'm5'))],
('n1', 'm1'): [('L', ('n1', 'm2'), (None, None))],
('n1', 'm2'): [('T', ('n2', 'm2'), ('n3', 'm4'))],
('n2', 'm2'): [('C', (None, None), (None, None))],
('n4', 'm5'): [('C', (None, None), (None, None))],
('n5', 'm5'): [('C', (None, None), (None, None))],
('n6', 'm6'): [('C', (None, None), (None, None))],
('n3', 'm4'): [('S', ('n4', 'm5'), ('n6', 'm6'))]}

# a reconciliation with no temporal inconsistency with duplication on a leave
host_tree_2 = { 'hTop': ('Top', 'm0', ('m0', 'm1'), ('m0', 'm2')),
('m0', 'm1'): ('m0', 'm1', None, None),
('m0', 'm2'): ('m0', 'm2', ('m2', 'm3'), ('m2', 'm4')),
('m2', 'm3'): ('m2', 'm3', None, None),
('m2', 'm4'): ('m2', 'm4', None, None)}

parasite_tree_2 = { 'pTop': ('Top', 'n0', ('n0', 'n1'), ('n0', 'n2')),
('n0', 'n1'): ('n0', 'n1', None, None),
('n0', 'n2'): ('n0', 'n2', ('n2', 'n3'), ('n2', 'n4')),
('n2', 'n3'): ('n2', 'n3', None, None),
('n2', 'n4'): ('n2', 'n4', None, None)}

reconciliation_2 = { ('n0', 'm4'): [('D', ('n1', 'm4'), ('n2', 'm4'))],
('n1', 'm4'): [('C', (None, None), (None, None))],
('n2', 'm4'): [('D', ('n3', 'm4'), ('n4', 'm4'))],
('n3', 'm4'): [('C', (None, None), (None, None))],
('n4', 'm4'): [('C', (None, None), (None, None))]}

# a reconciliation with another type of temporal inconsistency
host_tree_3 = { 'hTop': ('Top', 'm0', ('m0', 'm1'), ('m0', 'm2')),
('m0', 'm1'): ('m0', 'm1', ('m1', 'm3'), ('m1', 'm4')),
('m1', 'm3'): ('m1', 'm3', None, None),
('m1', 'm4'): ('m1', 'm4', None, None),
('m0', 'm2'): ('m0', 'm2', None, None)}

parasite_tree_3 = { 'pTop': ('Top', 'n0', ('n0', 'n4'), ('n0', 'n2')),
('n0', 'n4'): ('n0', 'n4', None, None),
('n0', 'n2'): ('n0', 'n2', ('n2', 'n5'), ('n2', 'n3')),
('n2', 'n5'): ('n2', 'n5', None, None),
('n2', 'n3'): ('n2', 'n3', ('n3', 'n1'), ('n3', 'n6')),
('n3', 'n1'): ('n3', 'n1', None, None),
('n3', 'n6'): ('n3', 'n6', None, None)}

reconciliation_3 = { ('n0', 'm4'): [('T', ('n4', 'm4'), ('n2', 'm2'))],
('n2', 'm2'): [('T', ('n5', 'm2'), ('n3', 'm1'))],
('n3', 'm1'): [('S', ('n1', 'm3'), ('n6', 'm4'))],
('n1', 'm3'): [('C', (None, None), (None, None))],
('n4', 'm4'): [('C', (None, None), (None, None))],
('n5', 'm2'): [('C', (None, None), (None, None))],
('n6', 'm4'): [('C', (None, None), (None, None))]}

# a reconciliation that is temporally consistent with more interwoven order
host_tree_4 = { 'hTop': ('Top', 'm0', ('m0', 'm1'), ('m0', 'm4')),
('m0', 'm1'): ('m0', 'm1', ('m1', 'm2'), ('m1', 'm3')),
('m0', 'm4'): ('m0', 'm4', ('m4', 'm5'), ('m4', 'm6')),
('m1', 'm2'): ('m1', 'm2', None, None),
('m1', 'm3'): ('m1', 'm3', None, None),
('m4', 'm5'): ('m4', 'm5', None, None),
('m4', 'm6'): ('m4', 'm6', None, None)}

parasite_tree_4 = { 'pTop': ('Top', 'n0', ('n0', 'n1'), ('n0', 'n2')),
('n0', 'n1'): ('n0', 'n1', ('n1', 'n5'), ('n1', 'n6')),
('n0', 'n2'): ('n0', 'n2', ('n2', 'n3'), ('n2', 'n4')),
('n1', 'n5'): ('n1', 'n5', None, None),
('n1', 'n6'): ('n1', 'n6', None, None),
('n3', 'n7'): ('n3', 'n7', None, None),
('n3', 'n8'): ('n3', 'n8', None, None),
('n2', 'n3'): ('n2', 'n3', ('n3', 'n7'), ('n3', 'n8')),
('n2', 'n4'): ('n2', 'n4', None, None),}

reconciliation_4 = { ('n0', 'm0'): [('S', ('n1', 'm1'), ('n2', 'm4'))],
('n1', 'm1'): [('S', ('n5', 'm2'), ('n6', 'm3'))],
('n2', 'm4'): [('T', ('n4', 'm4'), ('n3', 'm1'))],
('n4', 'm4'): [('L', ('n4', 'm6'), (None, None))],
('n4', 'm6'): [('C', (None, None), (None, None))],
('n3', 'm1'): [('S', ('n7', 'm2'), ('n8', 'm3'))],
('n7', 'm2'): [('C', (None, None), (None, None))],
('n8', 'm3'): [('C', (None, None), (None, None))],
('n5', 'm2'): [('C', (None, None), (None, None))],
('n6', 'm3'): [('C', (None, None), (None, None))]}

host_list = [host_tree_1, host_tree_2, host_tree_3, host_tree_4]
parasite_list = [parasite_tree_1, parasite_tree_2, parasite_tree_3, parasite_tree_4]
reconciliation_graph_list = [reconciliation_1, reconciliation_2, reconciliation_3, reconciliation_4]
if_one_inconsistent = [True, False, True, False]

# test recon_graph that contains a single inconsistent reconciliation
for host_tree, parasite_tree, reconciliation_graph, correct_result in zip(host_list, parasite_list, reconciliation_graph_list, if_one_inconsistent):
    source_nodes = [list(reconciliation_graph.keys())[0]]
    inconsistent= One_Inconsistent_Recon(source_nodes, reconciliation_graph, host_tree, parasite_tree)
    assert(inconsistent == correct_result)
    print(inconsistent)

# TODO: test on recon_graph that contains multiple reconciliations