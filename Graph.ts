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
* @param timeout Maximum time (in seconds) to spend performing A\* search.
* @returns A search result, which contains the path from `start` to a node satisfying `goal` and the cost of this path.
*/
function aStarSearch<Node> (
    graph : Graph<Node>,
    start : Node,
    goal : (n:Node) => boolean,
    heuristics : (n:Node) => number,
    timeout : number
) : SearchResult<Node> {
        console.log("Beginning search");
	//the number represents g, the cost to get from start to this node
	//The second node is the parent, used to reconstruct the path
	var open:[Node, number, Node][]=[];
	var closed:[Node, number, Node][]=[];
	open.push([start,0, undefined]);  
        var begin = Date.now();
	while (open.length>0 && (Date.now()-begin)<=timeout*1000){
		//find the node with the least f (g+heuristic) on open list
		var index:number=0;
		var minf:number = open[index][1]+heuristics(open[index][0]);
		for (var i = 0; i<open.length;i++){
			if(minf>=open[i][1]+heuristics(open[i][0])){
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
			for (var j = 0; j<closed.length;j++){
				if(graph.compareNodes(closed[j][0],next)==0){
                                    //if(closed[j][1]<=q[1]+1)
					continue loop;
                                    //closed.splice(j,1);
				}
			}
			open.push([next,q[1]+1,q[0]]);
		} 
                closed.push(q);
	}
    throw "Open list empty but goal not reached.";
}


