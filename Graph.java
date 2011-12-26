import java.util.*;

/**
   Graph class for shortest path method.
   @author Andreas Grothey
   @version 08/01/04
 */

public class Graph{

    private ArrayList<String> vertices;
    private ArrayList<Edge> edges;
    private double dist[];
    private int from[];
    private int fromEdge[];
    private int to[];
    private String lastTo;
    private String lastFrom;

    /**
       Initialise the graph
     */
    Graph(){
	vertices = new ArrayList<String>();
	edges = new ArrayList<Edge>();
    }

    /**
       Add a vertex to the graph
       @param vert vertex to be added
     */
    public void addVertex(String vert){
	
	if (!vertices.contains(vert)){
	    System.out.println("Add Vertex: "+vert);
	    vertices.add(vert);
	}
    }

    /**
       Add an edge to the graph
       @param vert1 source vertex
       @param vert2 target vertex 
       @param cost  cost/length of edge
       @exception IllegalArgumentException thrown if one of the vertices does not exist
    */
    public void addEdge(String vert1, String vert2, double cost){
	int i1, i2;
	
	i1 = vertices.lastIndexOf(vert1);
	i2 = vertices.lastIndexOf(vert2);

	if (i1==-1) {
	    throw new IllegalArgumentException("Vertex "+vert1+" not in graph");
	}

	if (i2==-1) {
	    throw new IllegalArgumentException("Vertex "+vert2+" not in graph");
	}
	System.out.println("Add Edge: "+vert1+" - "+vert2+" : "+cost);
	
	Edge edge1 = new Edge();
	edge1.start = i1;
	edge1.end = i2;
	edge1.cost = cost;
	edges.add(edge1);
    }
    
    /**
       registers a new cost for an existing edge
       @param vert1 source vertex
       @param vert2 target vertex 
       @param cost  new cost/length of edge
       @exception IllegalArgumentException thrown if one of the vertices does not exist or edge has not been registered yet
     */
    public void newCost(String vert1, String vert2, double cost){
	int i1, i2;
	i1 = vertices.lastIndexOf(vert1);
	i2 = vertices.lastIndexOf(vert2);

	if (i1==-1) {
	    throw new IllegalArgumentException("Vertex "+vert1+" not in graph");
	}

	if (i2==-1) {
	    throw new IllegalArgumentException("Vertex "+vert2+" not in graph");
	}

	boolean found = false;
	int pos = 0; 
	while(!found&&pos<edges.size()){
	    Edge edge = (Edge) edges.get(pos);
	    if (edge.start == i1 && edge.end == i2) {
		edge.cost = cost;
		found = true;
	    }
	    pos++;
	}
	if (!found) {
	    throw new IllegalArgumentException("Edge not in Graph");
	}


    }
    /**
       registers a new cost for an existing edge
       @param i index of edge (edges are numbered in the order they were registered (starting at 0) 
       @param cost  new cost/length of edge
     */
    public void newCost(int i, double cost){
	Edge edge = (Edge) edges.get(i);
	edge.cost = cost;
	System.out.println("New Cost: "+vertices.get(edge.start)+" - "+vertices.get(edge.end)+" : "+cost);

    }

    public Edge getEdge(int i){
    	return (Edge) edges.get(i);
    }

    /**
       finds all shortest paths through the graph from start to target vertex and returns its length (uses Dijkstra's method)
       @param start start vertex of required shortest path
       @param target end vertex of shortest path
       @return length of the shortest path between start and target
     */
    public double getShortestPath(String start, String target){
	
	int i1, i2;

	i1 = vertices.lastIndexOf(start);
	i2 = vertices.lastIndexOf(target);
	lastTo = target;
	lastFrom = start;


	if (i1==-1) {
	    System.out.println("Vertex "+start+" not in graph");
	    return -1;
	}

	if (i2==-1) {
	    System.out.println("Vertex "+target+" not in graph");
	    return -1;
	}

	int i, next;
	double min_dist;
	int nvert = vertices.size();
	int nedge = edges.size();

	
	dist = new double[nvert];
	from = new int[nvert];
	fromEdge = new int[nvert];
	boolean done[] = new boolean[nvert];
	Edge dummy[] = new Edge[0];
	Edge edgeA[] = (Edge [])edges.toArray(dummy);
	Object vert;

	for(i=0;i<nvert;i++){
	    dist[i] = 1e+10;
	    done[i] = false;
	}

	//System.out.println("First look at Vertex "+vertices.get(i1));
	dist[i1] = 0.0;
	done[i1] = true;
	from[i1] = -1;
	fromEdge[i1] = -1;
	
	for(i=0;i<nedge;i++){
	    if (edgeA[i].start==i1){
		dist[edgeA[i].end] = edgeA[i].cost;
		from[edgeA[i].end] = i1;
		fromEdge[edgeA[i].end] = i;
	    }
	    if (edgeA[i].end==i1){
		dist[edgeA[i].start] = edgeA[i].cost;
		from[edgeA[i].start] = i1;
		fromEdge[edgeA[i].start] = i;
	    }
	}
	
	do{
	    next = -1;
	    min_dist = 1e+10;
	
	    for(i=0;i<nvert;i++){
		if (!done[i]&&(dist[i]<min_dist)){
		    next = i;
		    min_dist = dist[i];
		}
	    }
	    if (next==-1){
		// get here at end of Dijkstra: return length
		return dist[i2];
	    }

	    
	    //System.out.println("Next look at Vertex "+vertices.get(next)+
	    //"   "+dist[next]);
	    
	    for(i=0;i<nedge;i++){
		if (edgeA[i].start==next&&!done[edgeA[i].end]){
		    if (dist[edgeA[i].end] > dist[next]+edgeA[i].cost){
			dist[edgeA[i].end] = dist[next]+edgeA[i].cost;
			from[edgeA[i].end] = next;
			fromEdge[edgeA[i].end] = i;
		    }
		}
		if (edgeA[i].end==next&&!done[edgeA[i].start]){
		    if (dist[edgeA[i].start] > dist[next]+edgeA[i].cost){
			dist[edgeA[i].start] = dist[next]+edgeA[i].cost;
			from[edgeA[i].start] = next;
			fromEdge[edgeA[i].start] = i;
		    }
		}
	    }
	    done[next] = true;
	}
	while(1==1);		  
    }

    /**
       finds critical (longest) path through an acyclic graph
       @exception UnsupportedOperationException if graph is not acyclic
     */
    private void criticalPath(){
	int i;
	int it, inext;
	int nvert = vertices.size();
	int nedge = edges.size();
	dist = new double[nvert];
	int noSources[] = new int[nvert]; 
	to = new int[nvert]; 
	int todo = nvert;
	boolean done[] = new boolean[nvert];
	Edge edgeA[] = (Edge [])edges.toArray(new Edge[0]);

	//int it = vertices.lastIndexOf(target); 

	for(i=0;i<nvert;i++){
	    dist[i] = 0;
	    done[i] = false;
	    to[i] = -1;
	}
	
	for(i=0;i<nedge;i++){
	    noSources[edgeA[i].start]++;
	}

	do{
	    
	    /*for (i=0;i<nvert;i++){
	      System.out.println(i+" "+vertices.get(i)+":"+noSources[i]+" "+done[i]+" "+to[i]+" "+dist[i]);
		}*/
	    // find !done node with no sources
	    inext = -1;
	    for(i=0;i<nvert;i++){
		if (!done[i]&&noSources[i]==0) inext = i;
	    }
	    //System.out.println(vertices.get(inext));
	    if (inext==-1){
		throw new UnsupportedOperationException("Graph is not acyclic");
	    }

	    done[inext] = true;
	    todo--;
	    //dist[inext] = 0;
	    //to[inext] = -1;
	    for(i=0;i<nedge;i++){
		if (edgeA[i].end==inext){
		    noSources[edgeA[i].start]--;
		    if (dist[inext]+edgeA[i].cost>=dist[edgeA[i].start]){
			dist[edgeA[i].start] = dist[inext]+edgeA[i].cost;
			to[edgeA[i].start] = inext;
		    }
		}
	    }
	} while(todo>0);
	    
    }

    /**
       Get next vertex of (shortest - not working yet!)/critical path.
       @param from current vertex
       @return next vertex (null if no next vertex)
     */
    private String getNext(String from){
	int i = vertices.lastIndexOf(from);
	if (to[i]==-1) return null;
	return (String)vertices.get(to[i]);
    }

    /** get previous vertex on shortest path.
       @param from current vertex
       @return previous vertex (null if no previous vertex)
     */
    public String getPrevious(String from){
	int i = vertices.lastIndexOf(from);
	if (this.from[i]==-1) return null;
	return (String) vertices.get(this.from[i]);
    }

    /**
       get edge leading to this vertex on shortest path.
       @param to current vertex
       @return index of egde leading to this vertex (edges are indexed in the order they were registered, starting at 0)
     */
    public int getPreviousEdge(String to){
	int i = vertices.lastIndexOf(to);
	return fromEdge[i];
    }

    /** 
	get distance to vertex on shortest path or distance from this vertex to final one on critical path
	@param to current vertex 
	@return distance on critical/shortest path
     */
    private double getDist(Object to){
	int i1;
	i1 = vertices.lastIndexOf(to);
	return dist[i1];
    }
    
    /**
       returns all vertices on the shortest path to given vertex as an ArrayList.
       @param to current vertex
       @return path from/to current vertex
     */
    public ArrayList getPathTo(Object to){
	int i1, next;
	ArrayList<Object> path = new ArrayList<Object>();
	Object obj; 

	i1 = vertices.lastIndexOf(to);

	next = i1;
	obj = vertices.get(next);
	path.add(obj);
	next = from[next];
	while (next!=-1){
	    obj = vertices.get(next);
	    path.add(obj);
	    next = from[next];
	}
	return path;
    }
    
    /**
       returns a boolean array indicating for each edge whether it is used
       on the last calculated shortest path.
       The return array is a boolean array of dimension (no of edges)
       An array entry is true if the corresponding edge is used.
       Edges are numbered in the order in which they were registered.
       @param to final vertex of path 
       @return path to final vertex. */
    public boolean[] getUsedEdges(){
	int nedge = edges.size();
	boolean[] ret = new boolean[nedge];
	int edge;

	String point = lastTo;
	//System.out.print(point);
	while((edge = getPreviousEdge(point))>=0){
	    ret[edge] = true;
	    point = getPrevious(point);
	}
	
	return ret;
    }


    /**
       prints the last calculated shortest path to the screen
    */
    public void printPath(){
	String point = lastTo;
	String[] points = new String[vertices.size()];
	int n=0;
	int edge;

	points[n] = point;
	n++;
	while((point=getPrevious(point))!=null){
	    points[n] = point;
	    n++;
	}
	System.out.print(points[n-1]);
	for(int i=n-2;i>=0;i--)
	    System.out.print(" - "+points[i]);
	System.out.println("");
    }

    public String getPath(){
	StringBuffer out = new StringBuffer("");
	String point = lastTo;
	String[] points = new String[vertices.size()];
	int n=0;
	int edge;

	points[n] = point;
	n++;
	while((point=getPrevious(point))!=null){
	    points[n] = point;
	    n++;
	}
	out.append(points[n-1]);
	for(int i=n-2;i>=0;i--)
	    out.append(" - "+points[i]);
	return out.toString();
    }

    public String getEdgeName(int i)
    {
	Edge e = (Edge)edges.get(i);
	String name = ((String)vertices.get(e.start))+" - "+((String)vertices.get(e.end));
	return name;

    }

    /** 
	This is just a test method for the Graph class.
	The main method constructs a simple Graph and finds the shortest
	path.
    */
    public static void main(String args[]){
	Graph graph = new Graph();
	double cost;
	boolean[] used;
	int i, n;

	graph.addVertex("A");
	graph.addVertex("B");
	graph.addVertex("C");
	graph.addVertex("D");
	graph.addVertex("E");
	graph.addEdge("A","B",3.0);
	graph.addEdge("A","C",4.0);
	graph.addEdge("B","C",2.0);
	graph.addEdge("B","D",1.0);
	graph.addEdge("C","E",3.0);
	graph.addEdge("D","E",8.0);
	cost = graph.getShortestPath("D", "E");
	System.out.println("Shortest Path length: "+cost);	

	used = graph.getUsedEdges();

	for (i=0;i<used.length;i++){
	    Edge e = (Edge) graph.getEdge(i);
	    System.out.println(e.start+" - "+e.end+"  "+used[i]);
	}
    }


}




class Edge{
    public int start;
    public int end;
    public double cost;
    public boolean directed;
}

class Node{
    public Object obj;
    public boolean done;
    public double dist;
}
