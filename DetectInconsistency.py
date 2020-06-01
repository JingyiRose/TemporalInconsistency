from enum import Enum

class States(Enum):
    BEFORE =  0
    AFTER = 1
    BOTHWAY = 2
    UNKNOWN = 3

class Constraint:
    def __init__(self, state, index_1, index_2):
        self.state = state
        self.index_1 = index_1
        self.index_2 = index_2

def build_index_dict(host_tree, parasite_tree):
    index_dict = {}
    index = 0
    for edge_name in host_tree:
        edge_four_tuple = host_tree[edge_name]
        index_dict[edge_four_tuple[1]] = index
        index += 1
    for edge_name in parasite_tree:
        edge_four_tuple = parasite_tree[edge_name]
        index_dict[edge_four_tuple[1]] = index
        index += 1
    return index_dict


def add_parent_child_relation(tree, M, index):
    for edge in tree:
        edge_four_tuple = tree[edge]
        if edge_four_tuple[0] == "Top":
            continue
        parent, child = edge
        M[index[parent]][index[child]] = States.BEFORE
        M[index[child]][index[parent]] = States.AFTER

def add_ancestor_descendent_relation(M):
    """
    after calling add_parent_child_relation, we need to update the other
    entries to reflect all ancestor-descendent relations
    """
    for i in range(len(M)):
        for j in range(len(M)):
            state = M[i][j]
            if state == States.UNKNOWN:
                continue
            for node_1 in range(len(M)):
                # Implication 1: e.g. if node_1 > i > j, then node_1 > j
                if M[node_1][i] == state:
                    M[node_1][j] = state
                # Implication 2: e.g. if i > j > node_1, then i > node_1
                if M[j][node_1] == state:
                    M[i][node_1] = state 
                # M is a square matrix, so #row = #col
                for node_2 in range(len(M)):
                    # Implication 3: e.g. if node_1 > i > j > node_2, then node_1 > node_2
                    if M[node_1][i] == state and M[j][node_2] == state:
                        M[node_1][node_2] = state

def initialize(host_tree, parasite_tree, index):
    """
    initialize M to include all the parent-child temporal relations 
    from parasite_tree and host_tree
    """
    num_nodes = len(index)

    M = [[States.UNKNOWN for i in range(num_nodes)] for j in range(num_nodes)]
    add_parent_child_relation(host_tree, M, index)
    add_parent_child_relation(parasite_tree, M, index)
    add_ancestor_descendent_relation(M)
    return M

def createParentDict(H, P):
    """
    :param host_tree:  host tree dictionary
    :param parasite_tree:  parasite tree dictionary
    :return: A dictionary that maps the name of a child node to the name of its parent 
             for both the host tree and the parasite tree.
    """
    parent_dict = {}
    for edge_name in H:
        child_node = H[edge_name][1]
        parent_node = H[edge_name][0]
        parent_dict[child_node] = parent_node
    for edge_name in P:
        child_node = P[edge_name][1]
        parent_node = P[edge_name][0]
        parent_dict[child_node] = parent_node
    return parent_dict

def One_Inconsistent_Recon(source_nodes, recon_graph, host_tree, parasite_tree):
    """
    return true if there is at least one temporally inconsistent reconciliation in
    the reconciliation graph
    """
    index = build_index_dict(host_tree, parasite_tree)
    parent = createParentDict(host_tree, parasite_tree)
    for source_node in source_nodes:
        if One_Inconsistent_Recon_Helper(source_node, recon_graph, host_tree, parasite_tree, index, parent)[0]:
            return True
    return False

def One_Inconsistent_Recon_Helper(mapping_node, recon_graph, host_tree, parasite_tree, index, parent):
    """
    return true if there is at least one temporally inconsistent reconciliation in
    the sub-reconciliation-graph rooted at the source_node
    """
    # # Base case, occurs if being called on a child produced by a loss event
    if mapping_node == (None, None):
        return False, initialize(host_tree, parasite_tree, index)

    parasite, host = mapping_node
    M = []
    for event_node in recon_graph[mapping_node]:

        event_type, mapping_child_1, mapping_child_2 = event_node
        constraints = []
        host_parent = parent[host]
        # if event type is a loss, the parasite is not actually mapped to the host in final 
        # reconciliation, so there is no constraint implied by the mapping node or event
        if event_type == 'L':
            constraints = []
        else:
            # if the node_mapping is not a leaf_mapping, we add the first relation
            if event_type != 'C':
                constraints.append(Constraint(States.BEFORE, index[parasite], index[host]))
            # if the node_mapping is not a mapping onto the root of host tree, we add the second relation
            if host_parent != 'Top':
                constraints.append(Constraint(States.BEFORE, index[host_parent], index[parasite]))
            
            # if event is a transfer, then we add two more temporal relations
            if event_type == 'T':
                # get the mapping for the right child which is the transferred child
                right_child_parasite, right_child_host = mapping_child_2
                # since a transfer event is horizontal, we have these two implied relations
                constraints.append(Constraint(States.BEFORE, index[parent[right_child_host]], index[parasite]))
                # the second relation is only added if the right child mapping is not a leaf mapping
                if recon_graph[mapping_child_2][0][0]!='C':
                    constraints.append(Constraint(States.BEFORE, index[right_child_parasite], index[host]))
 
        # TODO have better error message that indicates where the inconsistency first occurs
        inconsistent_1, mapping_child_1_matrix = One_Inconsistent_Recon_Helper(mapping_child_1, recon_graph, host_tree, parasite_tree, index, parent)
        inconsistent_2, mapping_child_2_matrix = One_Inconsistent_Recon_Helper(mapping_child_2, recon_graph, host_tree, parasite_tree, index, parent)
        inconsistent_3, event_matrix = matrices_AND(mapping_child_1_matrix, mapping_child_2_matrix)
        inconsistent_4 = add_constraints(event_matrix, constraints)

        if inconsistent_1 or inconsistent_2 or inconsistent_3 or inconsistent_4:
            return True, event_matrix
        # initialize M to the first event_matrix
        if M == []:
            M = event_matrix
        else: M = matrices_OR(M, event_matrix)

    return False, M

def add_constraints(event_matrix, constraints):
    for constraint in constraints:
        if add_constraint(event_matrix, constraint):
            return True
    return False

def reverse_state(state):
    if state == States.BEFORE:
        return States.AFTER
    else:
        return States.BEFORE

def contradict(state_1, state_2):
    if state_1 == States.UNKNOWN or state_2 == States.UNKNOWN:
        return False
    if state_1 == States.BOTHWAY or state_1 == States.BOTHWAY:
        return True
    if state_1 != state_2:
        return True
    return False

# a little redundant with add_ancestor_descendent_relation, although in latter there is no inconsistency possible TODO
def trickle_down(M, i, j):
    state = M[i][j] # this is only BEFORE or AFTER
    for node_1 in range(len(M)):
        # Implication 1: e.g. if node_1 > i > j, then node_1 > j
        if M[node_1][i] == state:
            if contradict(M[node_1][j], state):
                return True
            M[node_1][j] = state

        # Implication 2: e.g. if i > j > node_1, then i > node_1
        if M[j][node_1] == state:
            if contradict(M[i][node_1], state):
                return True
            M[i][node_1] = state

        # M is a square matrix, so #row = #col
        for node_2 in range(len(M)):
            # Implication 3: e.g. if node_1 > i > j > node_2, then node_1 > node_2
            if M[node_1][i] == state and M[j][node_2] == state:
                if contradict(M[node_1][node_2], state):
                    return True
                M[node_1][node_2] = state
    return False
    
def add_constraint(event_matrix, constraint):
    state = constraint.state # can only be States.BEFORE in current implementation
    index_1 = constraint.index_1
    index_2 = constraint. index_2
    current_state = event_matrix[index_1][index_2]
    if current_state == States.BOTHWAY:
        return True
    if current_state == States.UNKNOWN:
        event_matrix[index_1][index_2] = state
        # relation comes in pairs
        event_matrix[index_2][index_1] = reverse_state(state)
        if trickle_down(event_matrix, index_1, index_2):
            return True
        if trickle_down(event_matrix, index_2, index_1):
            return True
        return False
    if current_state == state:
        return False
    return True # current_state and state 0,1 or 1,0

def matrices_AND(M_1, M_2):
    num_nodes = len(M_1)
    trickle_down_cells = []
    M = [[States.UNKNOWN for i in range(num_nodes)] for j in range(num_nodes)]
    for i in range(len(M)):
        for j in range(len(M)):
            state_1 = M_1[i][j]
            state_2 = M_2[i][j]
            if state_1 == state_2 and state_1 != States.BOTHWAY: # either 0, 0 or 1, 1 or 3, 3
                M[i][j] = state_1
            elif state_1 == States.UNKNOWN: # 3, x -> x
                M[i][j] = state_2
                # needed because if M_1 has a->b, M_2 has b->c, then a->c should be in M
                trickle_down_cells.append ((i, j))
            elif state_2 == States.UNKNOWN: # x, 3 -> x
                M[i][j] = state_1
                trickle_down_cells.append ((i, j))
            else:   # 0, 1 or 1, 0, or 2, (0,1,2), or (0,1,2), 2
                return True, M
    for cell in trickle_down_cells:
        i, j = cell
        if trickle_down(M, i, j):
            return True, M
    return False, M

def matrices_OR(M_1, M_2):
    num_nodes = len(M_1)
    M = [[States.UNKNOWN for i in range(num_nodes)] for j in range(num_nodes)]
    for i in range(len(M)):
        for j in range(len(M)):
            state_1 = M_1[i][j]
            state_2 = M_2[i][j]
            if state_1 == state_2:
                M[i][j] = state_1
            elif state_1 == States.UNKNOWN:
                M[i][j] = state_2
            elif state_2 == States.UNKNOWN:
                M[i][j] = state_1
            else:
                M[i][j] = States.BOTHWAY
     # there is no trickle down effect for OR operator       
    return M

