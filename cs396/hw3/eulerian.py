#! /usr/bin/env python3
import sys
from graph import Graph

class NotConnected(Exception):
    pass
class OddDegree(Exception):
    pass

class UndirectedGraph:
    def __init__(self, graph):
        self.nodes = [ node.getName() for node in graph.getNodes() ]
        self.num_nodes = len(self.nodes)
        self.node_mapping = {}
        i = 0
        for node in self.nodes:
            self.node_mapping[node] = i
            i += 1
        self.matrix = [[0] * self.num_nodes for i in range(self.num_nodes)]
        for arc in graph.getArcs():
            start = arc.getStart().getName()
            finish = arc.getFinish().getName()
            self.matrix[self.node_mapping[start]][self.node_mapping[finish]] += 1

    def getNeighbors(self, node):
        res = {}
        i = 0
        for arc_count in self.matrix[self.node_mapping[node]]:
            if arc_count > 0:
                res[self.nodes[i]] = arc_count
            i += 1
        return res

    def getNeighbor(self, node):
        i = 0
        for arc_count in self.matrix[self.node_mapping[node]]:
            if arc_count > 0:
                return self.nodes[i]
            i += 1
        return None

    def use_arc(self, start, finish):
        old = self.matrix[self.node_mapping[start]][self.node_mapping[finish]]
        self.matrix[self.node_mapping[start]][self.node_mapping[finish]] = max(0, old - 1)
        self.matrix[self.node_mapping[finish]][self.node_mapping[start]] = max(0, old - 1)

    def __str__(self):
        res = "  "
        for node in self.nodes:
            res += str(node)
        res += "\n"
        for y in range(0, self.num_nodes):
            res += str(self.nodes[y]) + " " + y * " ";
            for x in range(y, self.num_nodes):
                res += str(self.matrix[y][x])
            res += "\n"
        return res


def is_eulerian(graph, start):
    """
    A test to see if a graph is eulerian
    We need to ensure the graph is connected and that every node has an even degree
    """
    visited = set()
    toVisit = [ start ]
    while 0 < len(toVisit):
        node = toVisit.pop()
        if node in visited:
            continue
        neighbors = graph.getNeighbors(node)
        degree = 0
        for arc_count in neighbors.values():
            degree += arc_count
        if degree % 2 != 0:
            raise OddDegree()
        visited.add(node)
        toVisit.extend(neighbors.keys())
    if len(visited) != graph.num_nodes:
        raise NotConnected()

def circuit(graph, start):
    path = [ ]
    toVisit = [ start ]
    while 0 < len(toVisit):
        curr = toVisit[len(toVisit) - 1]
        neighbor = graph.getNeighbor(curr)
        if neighbor is None:
            path.append(toVisit.pop())
        else:
            toVisit.append(neighbor)
            graph.use_arc(curr, neighbor)
    return path

def eulerian(graph):
  nodes = graph.nodes
  if len(nodes) == 0:
      return []
  start = nodes[0]
  is_eulerian(graph, start)
  return circuit(graph, start)

def main():
    g = Graph()
    if len(sys.argv) != 2:
        print("Missing command line argument")
        print("usage: ./eulerian.py [FILE]")
        sys.exit()
    g.load(sys.argv[1])
    try:
        u = UndirectedGraph(g)
        print(u)
        path = eulerian(u)
        print(path)
    except NotConnected:
        print("No eulerian circuit")
        print("Graph is not fully connected")
    except OddDegree:
        print("No eulerian circuit")
        print("Graph has a node with an odd degree")

if __name__ == "__main__":
    main()
