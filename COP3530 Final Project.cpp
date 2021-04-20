#include <boost/graph/adjacency_list.hpp>
#include <boost/pending/property.hpp>
#include <boost/config.hpp>
#include <boost/container_hash/hash.hpp>
#include <boost/graph/prim_minimum_spanning_tree.hpp>
#include <boost/graph/random.hpp>
#include <boost/random.hpp>
#include <boost/random/uniform_int_distribution.hpp>
#include <boost/graph/graphviz.hpp>
#include <iostream>
#include <iterator>
#include <algorithm>
#include <unordered_set>
#include <queue>
#include <vector>
#include <chrono>
#include <ctime>
#include <cstdint>
#include <stack>
#include <stdexcept>  
#include <tuple>
#include <boost/graph/dijkstra_shortest_paths.hpp>
#include <boost/bind/bind.hpp>
#include <libs/graph/src/read_graphviz_new.cpp>


using namespace std;
using namespace boost::placeholders;

typedef boost::property<boost::edge_weight_t, int> EdgeWeightProperty;

typedef boost::adjacency_list< boost::listS,
	boost::vecS,
	boost::undirectedS,
	boost::no_property,
	EdgeWeightProperty > Graph;

typedef typename boost::graph_traits<Graph>::vertex_descriptor Vertex;
typedef typename boost::graph_traits<Graph>::edge_descriptor Edge;

typedef boost::graph_traits<Graph>::edge_iterator edge_iterator;
typedef boost::graph_traits<Graph>::vertex_iterator vertex_iterator;

struct EdgeWeightPropertyT {
	typedef EdgeWeightProperty EdgeWeightPropertyTag;
};

Graph PrimAlgorithm(Graph g) {
	Graph out;
	//maps edge iterators to edge weights
	boost::property_map <Graph, boost::edge_weight_t>::type EdgeWeightMap = get(boost::edge_weight, g);
	//vertices which are not connected
	unordered_set<int> notConnected;
	//vertices which are connected
	unordered_set<int> connected;

	auto ei = edges(g);

	//insert all vertices into notConnected
	for (edge_iterator it = ei.first; it != ei.second; ++it) {
		int weight = EdgeWeightMap[*it];
		int source = boost::source(*it, g);
		int target = boost::target(*it, g);
		notConnected.insert(source);
		notConnected.insert(target);

	}
	
	//0 will be the source vertex
	connected.insert(0);
	int next = 0;

	
	//min heap ordering edges by weight
	priority_queue<pair<int, pair<int, int>>, vector<pair<int, pair<int, int>>>, greater<>> minHeap;
	//while there are not connected vertices (until there is one component)
	while (notConnected.size() > 0) {
		auto oei = boost::out_edges(next, g);

		//for each edge connecting to the next vertex
		for (auto it = oei.first; it != oei.second; ++it) {
			int weight = EdgeWeightMap[*it];
			int source = boost::source(*it, g);
			int target = boost::target(*it, g);
			//if the edge goes to a vertex that is not connected, put it in the heap
			if (connected.count(target) == 0) {
					minHeap.emplace(make_pair(weight, make_pair(source, target)));
			}
		}
		pair<int, pair<int, int>> leastWeight;
		//while there are edges in the heap
		while (minHeap.size() > 0) {
			leastWeight = minHeap.top();
			minHeap.pop();
			//if the target vertex of the least weight node is not already connected, break here so we choose this edge
			if (connected.count(leastWeight.second.second) == 0) {
				break;
			}
		}
		int weight = leastWeight.first;
		int source = leastWeight.second.first;
		int target = leastWeight.second.second;
		//add leastWeight as an edge to the minimum spanning tree
		boost::add_edge(source, target, weight, out);
		//now the source and target vertices are connected and not not connected
		notConnected.erase(source);
		notConnected.erase(target);
		connected.insert(source);
		connected.insert(target);
		//the next node is now the target of the edge. The heap stays the same, so we now only add the new adjacent edges to the heap and the rest remain
		next = target;


	}

	return out;
}





Graph BoruvkaAlgorithm(Graph g) {
	Graph out;

	//maps edge iterators to edge weights
	boost::property_map <Graph, boost::edge_weight_t>::type EdgeWeightMap = get(boost::edge_weight, g);
	//unordered set of sets of ints. These sets are the connected components of the graph
	unordered_set<set<int>, boost::hash<set<int>>> components;
	//maps source and target vertex to edge weight
	unordered_map<pair<int, int>, int, boost::hash<pair<int, int>>> edgeToWeight;
	//maps a component to the lowest weight (henceforth also cheapest) edge that connects it to a different component
	unordered_map<set<int>, pair<int, int>, boost::hash<set<int>>> componentCheapEdge;
	//unordered set of edges already added to the minimum spanning tree
	unordered_set<pair<int, int>, boost::hash<pair<int, int>>> edgesAdded;
	//unordered set of all vertices
	unordered_set<int> vertexSet;

	auto vi = vertices(g);
	auto ei = edges(g);

	//for each vertex, put the vertex in a component by itself, set its cheapest edge to a null value, and insert the vertex to the vertex set
	for (vertex_iterator it = vi.first; it != vi.second; ++it) {
		int vertex = *it;
		set<int> vertexComponent;
		vertexComponent.insert(vertex);
		components.insert(vertexComponent);
		componentCheapEdge[vertexComponent] = make_pair(-1, -1);
		vertexSet.insert(vertex);
	}

	//for each edge, map the edge forwards and backwards (as we use undirected graphs) to its edge weight
	for (edge_iterator it = ei.first; it != ei.second; ++it) {
		int weight = EdgeWeightMap[*it];
		int source = boost::source(*it, g);
		int target = boost::target(*it, g);
		edgeToWeight[make_pair(source, target)] = weight;
		edgeToWeight[make_pair(target, source)] = weight;
	}

	//while there is more than one connected component (until there is only one connected component)
	while (components.size() > 1) {
		//maps vertices to their components
		unordered_map<int, set<int>> componentMap;

		//for each vertex in the graph, map the vertex to the component it is in. Also set the cheapest edge of the component back to a null value
		for (auto c : components) {
			for (auto v : c) {
				componentMap[v] = c;
			}
			componentCheapEdge[c] = make_pair(-1, -1);
		}

		//for each edge in the graph
		for (edge_iterator it = ei.first; it != ei.second; ++it) {
			int weight = EdgeWeightMap[*it];
			int source = boost::source(*it, g);
			int target = boost::target(*it, g);
			
			auto componentSource = componentMap[source];
			auto componentTarget = componentMap[target];

			//if the edge lies between two different components
			if (componentSource != componentTarget) {
				auto componentSourceCheapEdge = componentCheapEdge[componentSource];
				//if the cheapest edge of the component of the source vertex is null or has greater weight than the current edge, then set its cheapest edge to this one
				if (componentSourceCheapEdge == make_pair(-1, -1) || weight < edgeToWeight[componentSourceCheapEdge]) {
					componentCheapEdge[componentSource] = make_pair(source, target);
				}
				//if the cheapest edge of the component of the target vertex is null or has greater weight than the current edge, then set its cheapest edge to this one

				auto componentTargetCheapEdge = componentCheapEdge[componentTarget];
				if (componentTargetCheapEdge == make_pair(-1, -1) || weight < edgeToWeight[componentTargetCheapEdge]) {
					componentCheapEdge[componentTarget] = make_pair(source, target);
				}
			}
		}
		//these allow us to update the "merging" of components while still iterating through the components
		auto newComponents = components;
		auto newComponentMap = componentMap;
		//for each component in the graph
		for (auto c : components) {
			auto cCheapEdge = componentCheapEdge[c];
			int source = cCheapEdge.first;
			int target = cCheapEdge.second;

			//if the component has a non-null cheapest edge (which it should have)
			if (cCheapEdge != make_pair(-1, -1)) {





				auto componentSource = componentMap[source];
				auto componentTarget = componentMap[target];

				int weight = edgeToWeight[make_pair(source, target)];
				//if this edge has not already been added to the minimum spanning tree, then add it to the minimum spanning tree
				if (edgesAdded.count(make_pair(source, target)) == 0) boost::add_edge(source, target, weight, out);
				//add this edge to the set of edges which have been already added
				edgesAdded.insert(make_pair(source, target));

				auto newComponentSource = newComponentMap[source];
				auto newComponentTarget = newComponentMap[target];

				//if the edge connects two different components
				if (newComponentSource != newComponentTarget) {
					//union the two sets together
					set<int> newComponentUnion;
					newComponentUnion.insert(newComponentSource.begin(), newComponentSource.end());
					newComponentUnion.insert(newComponentTarget.begin(), newComponentTarget.end());
					//set each vertex in either of the two original sets to map to the new union component
					for (auto j : newComponentSource) {
						newComponentMap[j] = newComponentUnion;
					}
					for (auto j : newComponentTarget) {
						newComponentMap[j] = newComponentUnion;
					}
					//in the updating set of components, add the union component and erase the two old components
					newComponents.insert(newComponentUnion);
					newComponents.erase(newComponentSource);
					newComponents.erase(newComponentTarget);
				}
				

			}

		}
		//after the iteration is done, set the components to be the new components
		components = newComponents;
	}



	return out;
}




int main()
{
	Graph g;

	string input;

	while (true) {

		boost::property_map <Graph, boost::edge_weight_t>::type EdgeWeightMap = get(boost::edge_weight, g);
		getline(cin, input);
		int spaceIndex = input.find(" ");
		
		//for some reason, the read_graphviz function really wanted dynamic properties while the write_graphviz function refused them
		boost::dynamic_properties dp(boost::ignore_other_properties);
		dp.property("label", EdgeWeightMap);

		//insert the specified vertex into the graph

		//note: when manually inserting vertices it is necessary to insert a 0 vertex for the MST algorithms to work.
		if (input.substr(0, spaceIndex) == "insert") {
			string sourceString;
			string targetString;
			string weightString;

			input = input.substr(spaceIndex + 1);
			spaceIndex = input.find(" ");
			sourceString = input.substr(0, spaceIndex);
			input = input.substr(spaceIndex + 1);
			spaceIndex = input.find(" ");
			targetString = input.substr(0, spaceIndex);
			input = input.substr(spaceIndex + 1);
			spaceIndex = input.find(" ");
			weightString = input.substr(0, spaceIndex);


			int source = stoi(sourceString);
			int target = stoi(targetString);
			int weight = stoi(weightString);
			boost::add_edge(source, target, weight, g);
		}
		//remove the specified vertex from the graph
		if (input.substr(0, spaceIndex) == "remove") {
			string sourceString;
			string targetString;
			string weightString;

			input = input.substr(spaceIndex + 1);
			spaceIndex = input.find(" ");
			sourceString = input.substr(0, spaceIndex);
			input = input.substr(spaceIndex + 1);
			spaceIndex = input.find(" ");
			targetString = input.substr(0, spaceIndex);
			input = input.substr(spaceIndex + 1);
			spaceIndex = input.find(" ");
			weightString = input.substr(0, spaceIndex);


			int source = stoi(sourceString);
			int target = stoi(targetString);
			int weight = stoi(weightString);
			boost::remove_edge(source, target, g);
		}
		//set the graph back to empty
		else if (input == "clear") {
			g = Graph();
		}
		//print out the edges and edge weights
		else if (input == "print") {
			auto ei = edges(g);
			cout << endl << "Edges and associated edge weights: " << endl << endl;
			for (edge_iterator it = ei.first; it != ei.second; ++it) {
				cout << *it << " " << EdgeWeightMap(*it) << endl;
			}
			cout << endl << "Total number of edges: " << boost::num_edges(g) << endl;
		}
		//generate a random graph with specified number of vertices and edges. Edge weights are random, but only between 1-100. 
		//note: nowhere do the MST algorithms assert that the graph is connected, and neither do we here. We can generate a graph with sufficiently large
		//number of vertices to guarantee that the graph is connected, or read a graph that we know is connected.
		else if (input.substr(0, spaceIndex) == "random") {

			int oldEdges = boost::num_edges(g);

			string verticesString;
			string edgesString;

			input = input.substr(spaceIndex + 1);
			spaceIndex = input.find(" ");
			verticesString = input.substr(0, spaceIndex);
			input = input.substr(spaceIndex + 1);
			spaceIndex = input.find(" ");
			edgesString = input.substr(0, spaceIndex);

			int numVertices = stoi(verticesString);
			int numEdges = stoi(edgesString);

			std::time_t now = std::time(0);
			boost::random::mt19937  rng{ static_cast<std::uint32_t>(now) };
			boost::random::uniform_int_distribution<> dist{ 1, 100 };


			boost::generate_random_graph(g, numVertices, numEdges, rng, false, false);

			auto ei = edges(g);

			boost::property_map <Graph, boost::edge_weight_t>::type EdgeWeightMap;
			unordered_map<pair<int, int>, int, boost::hash<pair<int, int>>> edgeToWeight;

			for (edge_iterator it = ei.first; it != ei.second; ++it) {
				EdgeWeightMap[*it] = dist(rng);
			}
			cout << boost::num_edges(g) - oldEdges << " edges added" << endl;
		}
		//run each algorithm on the current graph, and print the edges and edge weights of the output MST's along with the sum of the minimum spanning tree edge weights
		else if (input == "run_comparison") {

			auto ei = edges(g);
			unordered_map<pair<int, int>, int, boost::hash<pair<int, int>>> edgeToWeight;


			for (edge_iterator it = ei.first; it != ei.second; ++it) {
				int weight = EdgeWeightMap[*it];
				int source = boost::source(*it, g);
				int target = boost::target(*it, g);
				edgeToWeight[make_pair(source, target)] = weight;
				edgeToWeight[make_pair(target, source)] = weight;
			}

			Graph o = PrimAlgorithm(g);
			ei = edges(o);

			int s1 = 0;
			cout << endl << "Prim's Algorithm edges and weights (in order): " << endl << endl;
			for (edge_iterator it = ei.first; it != ei.second; ++it) {
				int source = boost::source(*it, g);
				int target = boost::target(*it, g);
				s1 += edgeToWeight[make_pair(source, target)];
				cout << *it << " " << edgeToWeight[make_pair(source, target)] << endl;
			}
			cout << endl << "Sum of minimum spanning tree: " << s1 << endl;

			o = BoruvkaAlgorithm(g);
			ei = edges(o);

			int s2 = 0;
			cout << endl << "Boruvka's Algorithm edges and weights (in order): " << endl << endl;
			for (edge_iterator it = ei.first; it != ei.second; ++it) {
				int source = boost::source(*it, g);
				int target = boost::target(*it, g);
				s2 += edgeToWeight[make_pair(source, target)];
				cout << *it << " " << edgeToWeight[make_pair(source, target)] << endl;
			}
			cout << endl << "Sum of minimum spanning tree: " << s2 << endl;
		}
		//run each algorithm and print how much time each took
		else if (input == "time_comparison") {
			cout << endl;
			auto start = chrono::high_resolution_clock::now();
			Graph o = PrimAlgorithm(g);
			auto stop = chrono::high_resolution_clock::now();
			auto duration = chrono::duration_cast<chrono::microseconds>(stop - start);
			cout << "Prim's Algorithm took " << duration.count() << " microseconds." << endl;

			cout << endl;
			start = chrono::high_resolution_clock::now();
			o = BoruvkaAlgorithm(g);
			stop = chrono::high_resolution_clock::now();
			duration = chrono::duration_cast<chrono::microseconds>(stop - start);
			cout << "Boruvka's Algorithm took " << duration.count()  << " microseconds." << endl;

}
		//read a graph in dot format
		else if (input.substr(0, spaceIndex) == "read") {
			string filename;

			input = input.substr(spaceIndex + 1);
			spaceIndex = input.find(" ");
			filename = input.substr(0, spaceIndex);
			ifstream myfile;
			myfile.open(filename);
			boost::read_graphviz(myfile, g, dp);
			myfile.close();
		}
		//write the current graph into dot format
		else if (input.substr(0, spaceIndex) == "write") {
			string filename;

			input = input.substr(spaceIndex + 1);
			spaceIndex = input.find(" ");
			filename = input.substr(0, spaceIndex);
			ofstream myfile;
			myfile.open(filename);

			boost::write_graphviz(myfile, g, boost::default_writer(), boost::make_label_writer(EdgeWeightMap));
			myfile.close();
		}
}


	}

		






	
	

	
