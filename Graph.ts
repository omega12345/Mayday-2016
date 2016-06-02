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
        //UPDATE: The the first number is g, the second is the heuristic
	//The second node is the parent, used to reconstruct the path
	var open:[Node, number, number, Node][]=[];
	var closed:[Node, number, number, Node][]=[];
	open.push([start,0, heuristics(start), undefined]);  
        var begin = Date.now();
	while (open.length>0 && (Date.now()-begin)<=timeout*1000){
		//find the node with the least f (g+heuristic) on open list
		var index:number=0;
		var minf:number = open[index][1]+open[index][2];
		for (var i = 0; i<open.length;i++){
			if(minf>=open[i][1]+open[i][2]){
				index=i;
				minf=open[index][1]+open[index][2];
			}
		}
		var q:[Node, number, number, Node] = open.splice(index, 1)[0];
                if(goal(q[0])){
                            //at this point, reconstruct path and return
                            //there seems to be something the matter with the tests:
                            //they pass the reverse of the following instead of demanding the
                            //whole reconstruction
                            var p:Node[] = [q[0]];
                            var next=q[3];
                            while(next){
                                p.push(next);
                                for (var i =0; i<closed.length; i++){
                                    if(closed[i][0]==next){
                                        next=closed[i][3];
                                        break;
                                    }
                                }
                            }
                            p.reverse();
                            var result : SearchResult<Node> = {
        			path: p,
        			cost: q[1]
                            };
                            return result;
		}
		var edges:Edge<Node>[]= graph.outgoingEdges(q[0]);
		loop: for (var i=0; i<edges.length; i++){
			var next:Node = edges[i].to;
			//if the node is in open list with lower g (the heuristic being the same), skip.
			for (var j = 0; j<open.length;j++){
				if(graph.compareNodes(open[j][0],next)==0&&open[j][1]<=q[1]+1){
					continue loop;
				}
			}
			//same for the closed list
			for (var j = 0; j<closed.length;j++){
				if(graph.compareNodes(closed[j][0],next)==0){
					continue loop;
				}
			}
			open.push([next,q[1]+1,heuristics(next),q[0]]);
		} 
                closed.push(q);
	}
    if (Date.now()-begin>=timeout*1000)
        throw "Timed out.";
    throw "Open list empty but goal not reached.";
}