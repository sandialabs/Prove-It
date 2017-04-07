'''
A dependency graph is a directed acyclic graph of dependency relationships.
A Proof is a dependency graph of derivations steps.  An Expression is
also a sort of dependency graph where the expression "depends" upon
sub-expressions.  The inverse relationship of a dependency is a requirement.
'''

def orderedDependencyNodes(rootNode, requirementsFn):
    '''
    Given a "root node" of a directed acyclic graph and a function
    that returns the "requirements" of a node (the node "depends" upon
    its requirements), returns a list of the "nodes" that includes
    the root node and all nodes which the root node depends upon, directly
    or indirectly.  The list will be ordered in such a way that each node
    will only depend upon nodes that come later in the list (the root node
    will necessarily come first).
    '''
    # nodesWithRepeats allow duplicates dependent nodes in a first pass.
    # Remove the duplicates in a second pass below.
    queue = [rootNode]
    nodesWithRepeats = []
    while len(queue) > 0:
        nextNode = queue.pop(0)
        nodesWithRepeats.append(nextNode)
        queue += requirementsFn(nextNode)
    # Second pass: remove duplicates.  Requirements should always come later 
    # (presenting the graph in a way that guarantees that it is acyclic).
    visited = set()
    enumeratedNodes = []
    for node in reversed(nodesWithRepeats):
        if node in visited:
            continue
        enumeratedNodes.insert(0, node)
        visited.add(node)
    return enumeratedNodes  