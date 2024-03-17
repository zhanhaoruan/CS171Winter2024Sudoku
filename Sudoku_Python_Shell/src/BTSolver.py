import SudokuBoard
import Variable
import Domain
import Trail
import Constraint
import ConstraintNetwork
import time
import random

class BTSolver:

    # ==================================================================
    # Constructors
    # ==================================================================

    def __init__ ( self, gb, trail, val_sh, var_sh, cc ):
        self.network = ConstraintNetwork.ConstraintNetwork(gb)
        self.hassolution = False
        self.gameboard = gb
        self.trail = trail

        self.varHeuristics = var_sh
        self.valHeuristics = val_sh
        self.cChecks = cc
        self.MRVtracks = []
        self.MRVinit = False

    # ==================================================================
    # Consistency Checks
    # ==================================================================

    # Basic consistency check, no propagation done
    def assignmentsCheck ( self ):
        for c in self.network.getConstraints():
            if not c.isConsistent():
                return False
        return True

    """
        Part 1 TODO: Implement the Forward Checking Heuristic

        This function will do both Constraint Propagation and check
        the consistency of the network

        (1) If a variable is assigned then eliminate that value from
            the square's neighbors.

        Note: remember to trail.push variables before you assign them
        Return: a tuple of a dictionary and a bool. The dictionary contains all MODIFIED variables, mapped to their MODIFIED domain.
                The bool is true if assignment is consistent, false otherwise.
    """
    def forwardChecking ( self , v ):
        if not v:
            #get the modified constraints
            for constraint in self.network.getModifiedConstraints():

                #get the already assigned variables first
                for var in constraint.vars:
                    if var.isAssigned():
                        value = var.getValues()[0]
                        for neighborvar in self.network.getNeighborsOfVariable(var):
                            if neighborvar.getDomain().contains(value):
                                if neighborvar.isAssigned():
                                    return ({}, False)
                                self.trail.push(neighborvar)
                                neighborvar.removeValueFromDomain(value)
                            if neighborvar.getDomain().isEmpty():
                                return ({}, False)
                        

            return ({}, True)
        else:
            value = v.getValues()[0]
            for neighborvar in self.network.getNeighborsOfVariable(v):
                if neighborvar.getDomain().contains(value) and not neighborvar.isAssigned():
                    self.trail.push(neighborvar)
                    neighborvar.removeValueFromDomain(value)
                if neighborvar.getDomain().isEmpty():
                    return ({}, False)
            return ({}, True)

    # =================================================================
	# Arc Consistency
	# =================================================================
    def arcConsistency( self ):
        assignedVars = []
        for c in self.network.constraints:
            for v in c.vars:
                if v.isAssigned():
                    assignedVars.append(v)
        while len(assignedVars) != 0:
            av = assignedVars.pop(0)
            for neighbor in self.network.getNeighborsOfVariable(av):
                if neighbor.isChangeable and not neighbor.isAssigned() and neighbor.getDomain().contains(av.getAssignment()):
                    neighbor.removeValueFromDomain(av.getAssignment())
                    if neighbor.domain.size() == 1:
                        neighbor.assignValue(neighbor.domain.values[0])
                        assignedVars.append(neighbor)

    
    """
        Part 2 TODO: Implement both of Norvig's Heuristics

        This function will do both Constraint Propagation and check
        the consistency of the network

        (1) If a variable is assigned then eliminate that value from
            the square's neighbors.

        (2) If a constraint has only one possible place for a value
            then put the value there.

        Note: remember to trail.push variables before you assign them
        Return: a pair of a dictionary and a bool. The dictionary contains all variables 
		        that were ASSIGNED during the whole NorvigCheck propagation, and mapped to the values that they were assigned.
                The bool is true if assignment is consistent, false otherwise.
    """
    def norvigCheck ( self, v ):
        if not v:
            #get the modified constraints
            for constraint in self.network.getModifiedConstraints():
                #get the already assigned variables first
                for var in constraint.vars:
                    if var.isAssigned():
                        value = var.getValues()[0]
                        for neighborvar in self.network.getNeighborsOfVariable(var):
                            if neighborvar.getDomain().contains(value):
                                if neighborvar.isAssigned():
                                    return ({}, False)
                                self.trail.push(neighborvar)
                                neighborvar.removeValueFromDomain(value)
                            if neighborvar.getDomain().isEmpty():
                                return ({}, False)
                        

            return ({}, True)
        else:
            value = v.getValues()[0]
            assignedVars = []
            for neighborvar in self.network.getNeighborsOfVariable(v):
                if neighborvar.getDomain().contains(value) and not neighborvar.isAssigned():
                    self.trail.push(neighborvar)
                    neighborvar.removeValueFromDomain(value)
                    if neighborvar.domain.size() == 1:
                        assignedVars.append(neighborvar)
                if neighborvar.getDomain().isEmpty():
                    return ({}, False)
            for var in assignedVars:
                self.trail.push(var)
                var.assignValue(var.domain.values[0])
                if not self.norvigCheck(var)[1]:
                    return ({}, False)
            return ({}, True)

    """
         Optional TODO: Implement your own advanced Constraint Propagation

         Completing the three tourn heuristic will automatically enter
         your program into a tournament.
     """
    def getTournCC ( self, v):
        return self.norvigCheck(v)

    # ==================================================================
    # Variable Selectors
    # ==================================================================

    # Basic variable selector, returns first unassigned variable
    def getfirstUnassignedVariable ( self ):
        for v in self.network.variables:
            if not v.isAssigned():
                return v

        # Everything is assigned
        return None

    """
        Part 1 TODO: Implement the Minimum Remaining Value Heuristic

        Return: The unassigned variable with the smallest domain
    """

    def MRV_comp_sort(v):
        return (v.isAssigned(), v.domain.size())

    def getMRV ( self ):
        if not self.MRVinit:
            for v in self.network.variables:
                if not v.isAssigned():
                    self.MRVtracks.append(v)
            self.MRVinit = True
        
        self.MRVtracks.sort(key=lambda variable: (variable.isAssigned(), variable.domain.size()))
        if self.MRVtracks[0].isAssigned():
            return None
        return self.MRVtracks[0]

    """
        Part 2 TODO: Implement the Minimum Remaining Value Heuristic
                       with Degree Heuristic as a Tie Breaker

        Return: The unassigned variable with the smallest domain and affecting the  most unassigned neighbors.
                If there are multiple variables that have the same smallest domain with the same number of unassigned neighbors, add them to the list of Variables.
                If there is only one variable, return the list of size 1 containing that variable.
    """
    def MRVwithTieBreaker ( self ):
        if not self.MRVinit:
            for v in self.network.variables:
                if not v.isAssigned():
                    self.MRVtracks.append(v)
            self.MRVinit = True
        
        self.MRVtracks.sort(key=lambda variable: (variable.isAssigned(), variable.domain.size()))
        if self.MRVtracks[0].isAssigned():
            return None
        domainSize = self.MRVtracks[0].size()
        constraintSize = len(self.network.getConstraintsContainingVariable(self.MRVtracks[0]))
        mostDegree = []
        for v in self.MRVtracks:
            if v.size() > domainSize:
                break
            currentConstraintsSize = len(self.network.getConstraintsContainingVariable(v))
            if currentConstraintsSize == constraintSize:
                mostDegree.append(v)
                continue
            if currentConstraintsSize > constraintSize:
                constraintSize == currentConstraintsSize
                mostDegree.clear()
                mostDegree.append(v)
        return mostDegree[0]

    """
         Optional TODO: Implement your own advanced Variable Heuristic

         Completing the three tourn heuristic will automatically enter
         your program into a tournament.
     """
    def getTournVar ( self ):
        return self.MRVwithTieBreaker()

    # ==================================================================
    # Value Selectors
    # ==================================================================

    # Default Value Ordering
    def getValuesInOrder ( self, v ):
        values = v.domain.values
        return sorted( values )

    """
        Part 1 TODO: Implement the Least Constraining Value Heuristic

        The Least constraining value is the one that will knock the least
        values out of it's neighbors domain.

        Return: A list of v's domain sorted by the LCV heuristic
                The LCV is first and the MCV is last
    """
    def getValuesLCVOrder ( self, v ):
        check_dict = {}
        for value in v.getValues():
            check_dict[value] = 1

        for neighbor in self.network.getNeighborsOfVariable(v):
            for value in v.getValues():
                if neighbor.getDomain().contains(value):
                    check_dict[value] += 1

        sorted_values = sorted(check_dict.items(), key=lambda item: item[1])
        return [item[0] for item in sorted_values]

    """
         Optional TODO: Implement your own advanced Value Heuristic

         Completing the three tourn heuristic will automatically enter
         your program into a tournament.
     """
    def getTournVal ( self, v ):
        return self.getValuesLCVOrder(v)

    # ==================================================================
    # Engine Functions
    # ==================================================================

    def solve ( self, time_left=600):
        if time_left <= 60:
            return -1

        start_time = time.time()
        if self.hassolution:
            return 0

        # Variable Selection
        v = self.selectNextVariable()

        # check if the assigment is complete
        if ( v == None ):
            # Success
            self.hassolution = True
            return 0

        # Attempt to assign a value
        for i in self.getNextValues( v ):

            # Store place in trail and push variable's state on trail
            self.trail.placeTrailMarker()
            self.trail.push( v )

            # Assign the value
            v.assignValue( i )

            # Propagate constraints, check consistency, recur
            if self.checkConsistency(v):
                elapsed_time = time.time() - start_time 
                new_start_time = time_left - elapsed_time
                if self.solve(time_left=new_start_time) == -1:
                    return -1
                
            # If this assignment succeeded, return
            if self.hassolution:
                return 0

            # Otherwise backtrack
            self.trail.undo()
        
        return 0

    def checkConsistency ( self , v=None):
        if self.cChecks == "forwardChecking":
            return self.forwardChecking(v)[1]

        if self.cChecks == "norvigCheck":
            return self.norvigCheck(v)[1]

        if self.cChecks == "tournCC":
            return self.getTournCC(v)[1]

        else:
            return self.assignmentsCheck()

    def selectNextVariable ( self ):
        if self.varHeuristics == "MinimumRemainingValue":
            return self.getMRV()

        if self.varHeuristics == "MRVwithTieBreaker":
            return self.MRVwithTieBreaker()

        if self.varHeuristics == "tournVar":
            return self.getTournVar()

        else:
            return self.getfirstUnassignedVariable()

    def getNextValues ( self, v ):
        if self.valHeuristics == "LeastConstrainingValue":
            return self.getValuesLCVOrder( v )

        if self.valHeuristics == "tournVal":
            return self.getTournVal( v )

        else:
            return self.getValuesInOrder( v )

    def getSolution ( self ):
        return self.network.toSudokuBoard(self.gameboard.p, self.gameboard.q)
