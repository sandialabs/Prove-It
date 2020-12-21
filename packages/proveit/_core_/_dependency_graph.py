'''
A dependency graph is a directed acyclic graph of dependency relationships.
A Proof is a dependency graph of derivations steps.  An Expression is
also a sort of dependency graph where the expression "depends" upon
sub-expressions.  The inverse relationship of a dependency is a requirement.
'''

def ordered_dependency_nodes(root_node, requirements_fn):
    '''
    Given a "root node" of a directed acyclic graph and a function
    that returns the "requirements" of a node (the node "depends" upon
    its requirements), returns a list of the "nodes" that includes
    the root node and all nodes which the root node depends upon, directly
    or indirectly.  The list will be ordered in such a way that each node
    will only depend upon nodes that come later in the list (the root node
    will necessarily come first).
    '''
    # nodes_with_repeats allows duplicate dependent nodes in a first pass.
    # Remove the duplicates in a second pass below.
    queue = [root_node]
    nodes_with_repeats = []
    while len(queue) > 0:
        next_node = queue.pop(0)
        nodes_with_repeats.append(next_node)
        queue.extend(requirements_fn(next_node))
    # Second pass: remove duplicates.  Requirements should always come later 
    # (presenting the graph in a way that guarantees that it is acyclic).
    visited = set()
    enumerated_nodes = []
    for node in reversed(nodes_with_repeats):
        if node in visited:
            continue
        enumerated_nodes.insert(0, node)
        visited.add(node)
    return enumerated_nodes  