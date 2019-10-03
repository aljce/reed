# File: routing.py

"""
This module defines a routing table for the ARPANET routing assignment.
Your job in this assignment is to implement the RoutingTable class so
its methods implement the functionality described in the comments.
"""

class Extended:
    """
    ℕ ∪ { ∞ } with the following properties
    ∀ x ∈ ℕ. x < ∞
    ∀ x. x + ∞ = ∞
    """
    def __init__(self, n):
        self.isInf = False
        self.n = n
    @staticmethod
    def infinity():
        inf = Extended(None)
        inf.isInf = True
        return inf
    def isInfinity(self):
        return self.isInf
    def __add__(self, other):
        if self.isInfinity():
            return Extended.infinity()
        else:
            if other.isInfinity():
                return Extended.infinity()
            else:
                return Extended(self.n + other.n)
    def __lt__(self, other):
        if self.isInfinity():
            return False
        else:
            if other.isInfinity():
                return True
            else:
                return self.n < other.n
    def __str__(self):
        if self.isInfinity():
            return "∞"
        else:
            return str(self.n)


class Link:
    def __init__(self, best, hopCount = Extended(0)):
        self.best = best
        self.sequence = 0
        self.hopCount = hopCount

class RoutingTable:
    """
    This class implements a routing table, which keeps track of
    two data values for each destination node discovered so far:
    (1) the hop count between this node and the destination, and
    (2) the name of the first node along the minimal path.
    """

    def __init__(self, name):
        """
        Creates a new routing table with a single entry indicating
        that this node can reach itself in zero hops.
        """
        self.name = name
        self.timeStep = 0
        self.neighbors = {}
        self.routing = { name: Link(name) } # localhost

    def getNodeNames(self):
        """
        Returns an alphabetized list of the known destination nodes.
        """
        return self.routing.keys()

    def getHopCount(self, destination):
        """
        Returns the hop count from this node to the destination node.
        """
        return self.routing[destination].hopCount

    def getBestLink(self, destination):
        """
        Returns the name of the first node on the path to destination.
        """
        return self.routing[destination].best


    def update(self, source, table):
        """
        Updates this routing table based on the routing message just
        received from the node whose name is given by source.  The table
        parameter is the current RoutingTable object for the source.
        """
        TIMEOUT = 10

        # if self.name == "HARV" and self.timeStep == 20:
        #     for link in self.routing.values():
        #         link.hopCount = Extended(0)

        self.neighbors[source] = self.timeStep;
        for neighbor, lastHeard in list(self.neighbors.items()):
            if self.timeStep - lastHeard >= TIMEOUT:
                for link in self.routing.values():
                    if link.best == neighbor:
                        link.sequence += 1 # raise the current epoch
                        link.hopCount = Extended.infinity()
                del self.neighbors[neighbor]

        self.timeStep += 1

        max_sequence = 0

        for dest, link in table.routing.items():
            if dest in self.routing:
                cur = self.routing[dest]
                if self.name == cur.best: # localhost
                    continue
                lowerHopCount = link.sequence == cur.sequence and link.hopCount < cur.hopCount
                # Only consider lowering the hopCount if the entries are from the same epoch
                if link.sequence > cur.sequence or lowerHopCount:
                    cur.best = source
                    cur.sequence = link.sequence
                    cur.hopCount = link.hopCount + Extended(1)
                max_sequence = max(max_sequence, cur.sequence)
            else:
                self.routing[dest] = Link(source, link.hopCount + Extended(1))

        self.routing[self.name].sequence = max_sequence
        # raise localhost to the maximum known epoch
        # This allows for the network to find alternate paths after propagating a failure

