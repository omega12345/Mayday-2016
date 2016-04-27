///<reference path="lib/collections.ts"/>
///<reference path="lib/node.d.ts"/>

/** Graph module
*
*  Types for generic A\* implementation.
*
*  *NB.* The only part of this module
*  that you should change is the `aStarSearch` function. Everything
*  else should be used as-is.
*/

/** An edge in a graph. */
class Edge<Node> {
    from : Node;
    to   : Node;
    cost : number;
}

/** A directed graph. */
interface Graph<Node> {
    /** Computes the edges that leave from a node. */
    outgoingEdges(node : Node) : Edge<Node>[];
    /** A function that compares nodes. */
    compareNodes : collections.ICompareFunction<Node>;
}

/** Type that reports the result of a search. */
class SearchResult<Node> {
    /** The path (sequence of Nodes) found by the search algorithm. */
    path : Node[];
    /** The total cost of the path. */
    cost : number;
}

/**
* A\* search implementation, parameterised by a `Node` type. The code
* here is just a template; you should rewrite this function
* entirely. In this template, the code produces a dummy search result
* which just picks the first possible neighbour.
*
* Note that you should not change the API (type) of this function,
* only its body.
* @param graph The graph on which to perform A\* search.
* @param start The initial node.
* @param goal A function that returns true when given a goal node. Used to determine if the algorithm has reached the goal.
* @param heuristics The heuristic function. Used to estimate the cost of reaching the goal from a given Node.
* @param timeout Maximum time to spend performing A\* search.
* @returns A search result, which contains the path from `start` to a node satisfying `goal` and the cost of this path.
*/
function aStarSearch<Node> (
    graph : Graph<Node>,
    start : Node,
    goal : (n:Node) => boolean,
    heuristics : (n:Node) => number,
    timeout : number
) : SearchResult<Node> {
	//the number represents g, the cost to get from start to this node
	//The second node is the parent, used to reconstruct the path
	var open:[Node, number, Node][]=[];
	var closed:[Node, number, Node][]=[];
	open.push([start,0, undefined]);        
	while (open.length>0 && timeout>0){
                
                timeout--;
		//find the node with the least f (g+heuristic) on open list
		var index:number=0;
		var minf:number = open[index][1]+heuristics(open[index][0]);
		for (var i = 0; i<open.length;i++){
			if(minf>=open[i][1]){
				index=i;
				minf=open[index][1]+heuristics(open[index][0]);
			}
		}
		var q:[Node, number, Node] = open.splice(index, 1)[0];
		var edges:Edge<Node>[]= graph.outgoingEdges(q[0]);
		loop: for (var i=0; i<edges.length; i++){
			var next:Node = edges[i].to;
			if(goal(next)){
                            //at this point, reconstruct path and return
                            //there seems to be something the matter with the tests:
                            //they pass the reverse of the following instead of demanding the
                            //whole reconstruction
                            var p:Node[] = [next, q[0]];
                            next=q[2];
                            while(next){
                                p.push(next);
                                for (var i =0; i<closed.length; i++){
                                    if(closed[i][0]==next){
                                        next=closed[i][2];
                                        break;
                                    }
                                }
                            }
                            p.reverse();
                            var result : SearchResult<Node> = {
        			path: p,
        			cost: q[1]+1
                            };
                            return result;
			}
			//if the node is in open list with lower g (the heuristic
			//always being the same), skip.
			for (var j = 0; j<open.length;j++){
				if(graph.compareNodes(open[j][0],next)==0&&open[j][1]<=q[1]+1){
					continue loop;
				}
			}
			//same for the closed list
                        //console.log(closed.length);
			for (var j = 0; j<closed.length;j++){
				if(graph.compareNodes(closed[j][0],next)==0){
                                    if(closed[j][1]<=q[1]+1)
					continue loop;
                                    closed.splice(j,1);
				}
			}
			open.push([next,q[1]+1,q[0]]);
		} 
                closed.push(q);
	}
    throw "Open list empty but goal not reached.";
}


//////////////////////////////////////////////////////////////////////
// here is an example graph

interface Coordinate {
    x : number;
    y : number;
}


class GridNode {
    constructor(
        public pos : Coordinate
    ) {}

    add(delta : Coordinate) : GridNode {
        return new GridNode({
            x: this.pos.x + delta.x,
            y: this.pos.y + delta.y
        });
    }

    compareTo(other : GridNode) : number {
        return (this.pos.x - other.pos.x) || (this.pos.y - other.pos.y);
    }

    toString() : string {
        return "(" + this.pos.x + "," + this.pos.y + ")";
    }
}

/** Example Graph. */
class GridGraph implements Graph<GridNode> {
    private walls : collections.Set<GridNode>;

    constructor(
        public size : Coordinate,
        obstacles : Coordinate[]
    ) {
        this.walls = new collections.Set<GridNode>();
        for (var pos of obstacles) {
            this.walls.add(new GridNode(pos));
        }
        for (var x = -1; x <= size.x; x++) {
            this.walls.add(new GridNode({x:x, y:-1}));
            this.walls.add(new GridNode({x:x, y:size.y}));
        }
        for (var y = -1; y <= size.y; y++) {
            this.walls.add(new GridNode({x:-1, y:y}));
            this.walls.add(new GridNode({x:size.x, y:y}));
        }
    }

    outgoingEdges(node : GridNode) : Edge<GridNode>[] {
        var outgoing : Edge<GridNode>[] = [];
        for (var dx = -1; dx <= 1; dx++) {
            for (var dy = -1; dy <= 1; dy++) {
                if (! (dx == 0 && dy == 0)) {
                    var next = node.add({x:dx, y:dy});
                    if (! this.walls.contains(next)) {
                        outgoing.push({
                            from: node,
                            to: next,
                            cost: Math.sqrt(dx*dx + dy*dy)
                        });
                    }
                }
            }
        }
        return outgoing;
    }

    compareNodes(a : GridNode, b : GridNode) : number {
        return a.compareTo(b);
    }

    toString() : string {
        var borderRow = "+" + new Array(this.size.x + 1).join("--+");
        var betweenRow = "+" + new Array(this.size.x + 1).join("  +");
        var str = "\n" + borderRow + "\n";
        for (var y = this.size.y-1; y >= 0; y--) {
            str += "|";
            for (var x = 0; x < this.size.x; x++) {
                str += this.walls.contains(new GridNode({x:x,y:y})) ? "## " : "   ";
            }
            str += "|\n";
            if (y > 0) str += betweenRow + "\n";
        }
        str += borderRow + "\n";
        return str;
    }
}
