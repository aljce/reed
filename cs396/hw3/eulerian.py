#! /usr/bin/env python3
import sys
from graph import Graph

class NotConnected(Exception):
    pass
class OddDegree(Exception):
    pass

class UndirectedGraph(Graph):
    def removeArc(self, arc):
        super().removeArc(arc)
        for rev in self.getArcs():
            if arc.getStart() == rev.getFinish() and arc.getFinish() == rev.getStart():
                super().removeArc(rev)
                break

def degree(node):
    return (len(node._arcsTo) + len(node._arcsFrom)) / 2

class Eulerian(UndirectedGraph):
    def __init__(self, graph):
        """
        A "smart constructor" for eulerian graphs
        Eulerian graphs are fully connected and every node has an even degree
        """
        self._nodes = graph._nodes
        self._arcs = graph._arcs
        nodes = self.getNodes()
        if len(nodes) == 0:
            return
        toVisit = [ nodes[0] ]
        visited = set()
        while 0 < len(toVisit):
            curr = toVisit.pop()
            if curr in visited:
                continue
            if degree(curr) % 2 != 0:
                raise OddDegree()
            neighbors = curr.getNeighbors()
            toVisit.extend(neighbors)
            visited.add(curr)
        if len(visited) != len(self):
            raise NotConnected

    def circuit(self):
        nodes = self.getNodes()
        if len(nodes) == 0:
            return []
        toVisit = [ nodes[0] ]
        path = []
        while 0 < len(toVisit):
            curr = toVisit[len(toVisit) - 1]
            arcs = curr.getArcs()
            if len(arcs) == 0:
                path.append(toVisit.pop())
            else:
                arc = arcs[0]
                toVisit.append(arc.getFinish())
                self.removeArc(arc)
        return path

def main():
    g = UndirectedGraph()
    if len(sys.argv) != 2:
        print("Missing command line argument")
        print("usage: ./eulerian.py [FILE]")
        sys.exit()
    g.load(sys.argv[1])
    try:
        path = Eulerian(g).circuit()
        print(path)
    except NotConnected:
        print("No eulerian circuit")
        print("Graph is not fully connected")
    except OddDegree:
        print("No eulerian circuit")
        print("Graph has a node with an odd degree")

if __name__ == "__main__":
    main()
