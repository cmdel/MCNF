import java.io.*;
import java.lang.reflect.Array;
import java.text.DecimalFormat;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.Vector;

import javax.sql.CommonDataSource;

/**
 * @author Christos M. Delivorias
 * 
 */
public class Mcnf {
	private static final double M = Math.pow(10, 4);
	private static int iter = 1;
	private static String[] path_names = new String[100];
	private static DecimalFormat number;
	private static HashMap<String, Integer> mp = new HashMap();
	private static boolean converged = false;
	private static double[][] matrixB;
	private static double[] cost;
	private static double[] solution;
	private static double[] multipliers;
	private static String[] solutions;

	/**
	 * Main method of the MCNF process
	 * 
	 * @param args
	 *            Arguments required is a filename with the data file. e.g.
	 *            smallnet.dat
	 * @throws Exception
	 *             Throws exception from the LP class.
	 */
	@SuppressWarnings("unchecked")
	public static void main(String[] args) throws Exception {
		FileReader file = new FileReader(args[0]);
		BufferedReader br = new BufferedReader(file);
		String line = br.readLine();
		StringTokenizer tokens = new StringTokenizer(line);

		// Read the first line with the initial vector capacities
		int vertices = new Integer(tokens.nextToken()).intValue();
		int edges = new Integer(tokens.nextToken()).intValue();
		int commodities = new Integer(tokens.nextToken()).intValue();
		Graph network = new Graph();
		double lambdas_star = 0;
		solutions = new String[100];

		System.out
				.println("=========================== Read in the Graph ===========================");
		// Add all available vertices to the graph
		for (int i = 0; i < vertices; i++) {
			String nextLine = br.readLine();
			tokens = new StringTokenizer(nextLine);
			network.addVertex(tokens.nextToken());
		}

		// Add all available edges to the graph
		Double[] capac = new Double[edges];
		Double[] costs = new Double[edges];
		for (int i = 0; i < edges; i++) {
			String nextLine = br.readLine();
			tokens = new StringTokenizer(nextLine);
			String source = tokens.nextToken();
			String target = tokens.nextToken();
			Double cost = new Double(tokens.nextToken()).doubleValue();
			network.addEdge(source, target, cost);
			costs[i] = cost;
			capac[i] = Double.parseDouble(tokens.nextToken());
		}
		// Hold all commodities in a 2-dimensional vector.
		String[][] commod = new String[commodities][];
		for (int i = 0; i < commodities; i++) {
			String nextLine = br.readLine();
			tokens = new StringTokenizer(nextLine);
			String source = tokens.nextToken();
			String target = tokens.nextToken();
			String amount = tokens.nextToken();
			commod[i] = new String[] { source, target, amount };
		}
		// The number of commodities
		int commoditiesItems = commod.length;

		// Construct the Danzig-Wolfe problem
		// Begin with the bounding arrays
		double[] rl = new double[edges + commoditiesItems];
		double[] ru = new double[edges + commoditiesItems];

		// Populate the boundaries with their fixed values
		for (int i = 0; i < rl.length - commoditiesItems; i++) {
			rl[i] = 0.0;
			ru[i] = capac[i];
		}

		for (int i = rl.length - commoditiesItems; i < rl.length; i++) {
			ru[i] = 1.0;
			rl[i] = 1.0;
		}

		// Create the matrix of paths and constraints
		Vector[] matrixA = new Vector[100];

		boolean[][] paths = new boolean[commoditiesItems][edges];
		for (int i = 0; i < paths.length; i++) {
			for (int j = 0; j < paths[i].length; j++) {
				paths[i][j] = false;
			}
		}

		// Initialize the lambda multipliers to 0
		double[] lambdas = new double[edges];

		// Create the vector of the objective coefficients
		Vector objCoeff = new Vector(10);

		generate_column(paths, matrixA, costs, capac, objCoeff, commod);

		// Change the coefficients of the dummy paths to M, very large.
		for (int i = 0; i < paths.length; i++) {
			objCoeff.set(i, M);
		}

		double prev_solution = M;
		Double[] newCosts = new Double[edges];
		for (int i = 0; i < edges; i++) {
			newCosts[i] = (Double) costs[i];
		}

		//
		// The convergence while loop
		//
		while (!converged) {
			path_names = new String[100];
			Arrays.fill(lambdas, (byte) 0);
			// Keep track of all paths
			int counter = get_first_empty_space(matrixA);

			System.out.println("=============================== start DW iter "
					+ iter + "  ==========================");
			System.out.println();

			System.out
					.println("------------------------------ set new edge costs -------------------------");
			// Update the costs of all edges in the graph to Cj+|lj|
			for (int i = 0; i < costs.length; i++) {
				network.newCost(i, newCosts[i]);
			}
			System.out
					.println("------------- find new routes by solving shortest path problem  ------------");
			// Find shortest path on this graph.
			paths = solve_shortest_path(network, commod);

			generate_column(paths, matrixA, newCosts, capac, objCoeff, commod);

			// Keep track of all paths
			counter = get_first_empty_space(matrixA);

			// variables constraints
			double[] cl = new double[objCoeff.size()];
			double[] cu = new double[objCoeff.size()];
			for (int i = 0; i < cu.length; i++) {
				cl[i] = 0.0;
				cu[i] = 1.0;
			}

			// Formulate the LP
			matrixB = new double[matrixA.length][];
			cost = new double[objCoeff.size()];

			// Convert Vectors to arrays to pass into the LP solver
			cost = to_array(objCoeff);
			for (int i = 0; i < get_first_empty_space(matrixA); i++) {
				double[] tmp = to_array(matrixA[i]);
				matrixB[i] = tmp;
			}

			// Print out the reduced costs
			for (int i = 0; i < commoditiesItems; i++) {
				System.out.println("Routing demand " + i + ") " + commod[i][0]
						+ " - " + commod[i][1] + " : " + commod[i][2]);
				System.out.println("	Path: " + path_names[i]);
				double sum = getSums(
						mp.get(getKeysByValue(mp, i + commoditiesItems)),
						commoditiesItems, matrixB);
				System.out.println("	Cost (using original edge costs) = "
						+ cost[i + counter - commoditiesItems]);
				double cstar = get_cstar(i, matrixB, commod, lambdas_star);
				System.out.println("	RED_COST: cstar = " + cstar
						+ " col_cost = " + cost[i + counter - commoditiesItems]
						+ "=> red_cost = " + (sum - cstar));
				if (!converged)
					System.out.println("	=> add column "
							+ (i + counter - commoditiesItems) + " for demand "
							+ i);
				else
					System.out.println("	=> column not added \n"
							+ "No columns added =>D-W has converged!");
			}

			// Stop printing when the D-W has converged
			if (!converged) {
				// Transpose the matrix
				double[][] matrixC = new double[matrixB[0].length][get_first_empty_space(matrixA)];
				matrixC = transpose_matrix(matrixB, matrixA);

				System.out
						.println("---------------------------- solve DW Master LP ----------------------------");
				System.out.println("Calling LP solver EMSOL:");
				System.out
						.println("--------------------------- report LP solution -----------------------------");
				// Construct the LP solver
				LP lp = new LP(cost, matrixC, cl, cu, rl, ru, cost.length,
						edges + commoditiesItems);
				solution = lp.getSolution();

				// Return all the multipliers form the LP
				multipliers = lp.getMultipliers();

				// Extract the lambda for the edges
				for (int i = 0; i < edges; i++) {
					lambdas[i] -= multipliers[i + counter];
				}

				for (int j = 0; j < counter; j++) {
					lambdas_star = multipliers[j];
				}

				// Update the costs of all edges in the graph to Cj+|lj|
				for (int i = 0; i < costs.length; i++) {
					newCosts[i] = costs[i] + Math.abs(lambdas[i]);
				}

				// Create the vectors for each edges total use
				double[] edgeUse = new double[edges];
				Arrays.fill(edgeUse, (byte) 0);
				for (int i = commoditiesItems; i < solution.length; i++) {
					for (int j = 0; j < matrixB[commoditiesItems].length
							- commoditiesItems; j++) {
						edgeUse[j] += matrixB[i][j] * solution[i];
					}
				}

				System.out.println("Routes usage in LP solution:");
				for (int i = 0; i < commoditiesItems; i++) {
					System.out.println("	Dummy Route demand " + i + "	= "
							+ solution[i]);
				}
				for (int i = 0; i < mp.size(); i++) {
					System.out.println("	"
							+ getKeysByValue(mp, i + commoditiesItems) + "		= "
							+ solution[i + commoditiesItems]);
				}

				number = new DecimalFormat("0.0");
				System.out
						.println("Edge usage and multipliers in LP solution:");
				for (int i = 0; i < costs.length; i++) {
					System.out.println("edge " + network.getEdgeName(i) + ": "
							+ number.format(edgeUse[i]) + " / " + capac[i]
							+ "	" + lambdas[i]);
				}
				// Check if the solution has converged
				double diff = lp.getValue() - prev_solution;

				// Store the optimal solution for the next iteration check
				prev_solution = lp.getValue();

				// Keep track of all solution stats
				String s = "";
				s += "EMSOL: ifail= " + lp.getIfail() + ",";
				s += " f= " + lp.getValue() + ", ";
				s += "LP iters: " + lp.getIters();
				solutions[iter - 1] = s;
				// System.out.println(prev_solution);
				iter++;
			} else {
				// The iterations have converged so print out the solution
				System.out
						.println("================== Solution ==================");
				int[][] commod_paths = get_commods_paths(matrixB, commod);
				for (int i = 0; i < commod_paths.length; i++) {
					System.out.println("Routing demand " + i + ") "
							+ commod[i][0] + " - " + commod[i][1] + " : "
							+ commod[i][2]);
					for (int j2 = 0; j2 < commod_paths[i].length; j2++) {
						if (commod_paths[i][j2] != 0
								&& solution[commod_paths[i][j2]] != 0) {
							System.out.println(" Route " + commod_paths[i][j2]
									+ ": weight="
									+ solution[commod_paths[i][j2]] + ": cost="
									+ cost[commod_paths[i][j2]]);
							System.out.print("	Edges used:	");
							for (int j = 0; j < matrixB[j2].length
									- commoditiesItems; j++) {
								if (matrixB[commod_paths[i][j2]][j] != 0) {
									System.out.print(j + " ");

								}
							}
							System.out.print("\n");
						}
					}
				}
				for (int i = 0; i < solutions.length; i++) {
					if (solutions[i] != null)
						System.out.println(solutions[i]);
				}
			}
		}
	}// End of main Method

	/**
	 * Calculate the C* value for the reduced costs
	 * 
	 * @param i
	 * @param matrixB
	 * @param commod
	 * @param lambdas_star
	 * @return
	 */
	private static Double get_cstar(int i, double[][] matrixB,
			String[][] commod, double lambdas_star) {
		double sum = 0.0;
		int[][] commod_paths = get_commods_paths(matrixB, commod);
		for (int j = 0; j < commod_paths[i].length; j++) {
			sum += solution[commod_paths[i][j]]
					* (cost[commod_paths[i][j]] + getSums(commod_paths[i][j],
							commod.length, matrixB));
		}

		return sum;
	}

	/**
	 * Get the paths that correspond to each commodity in the matrix
	 * 
	 * @param matrixB
	 * @param commod
	 * @return
	 */
	private static int[][] get_commods_paths(double[][] matrixB,
			String[][] commod) {
		int[][] answer = new int[commod.length][10];
		for (int i = 0; i < commod.length; i++) {
			for (int j = 0; j < matrixB[i].length; j++) {
				// Find the row where this commodity appears first
				if (matrixB[i][j] == 1.0) {
					int t = 0;
					for (int j2 = 0; j2 < matrixB.length; j2++) {
						if (matrixB[j2] != null && matrixB[j2][j] == 1) {
							answer[i][t] = j2;
							t++;
						}
					}
				}
			}
		}
		return answer;
	}

	/**
	 * Transpose the provided matrix
	 * 
	 * @param matrixB
	 * @param matrixA
	 * @return
	 */
	private static double[][] transpose_matrix(double[][] matrixB,
			Vector[] matrixA) {
		double[][] matrixC = new double[matrixB[0].length][get_first_empty_space(matrixA)];
		for (int i = 0; i < get_first_empty_space(matrixA); i++) {
			for (int j = 0; j < matrixB[i].length; j++) {
				matrixC[j][i] = matrixB[i][j];
			}
		}
		return matrixC;
	}

	/**
	 * REtrieve the first empty space in an array
	 * 
	 * @param path_names2
	 * @return the index of the empty place
	 */
	private static int get_first_place(String[] path_names2) {
		for (int i = 0; i < path_names2.length; i++) {
			if (path_names2[i] == null)
				return i;
		}
		return -1;
	}

	/**
	 * Calculate the sums of all paths
	 * 
	 * @param i
	 * @param commoditiesItems
	 * @param matrixB
	 * @return
	 */
	private static double getSums(int i, int commoditiesItems,
			double[][] matrixB) {
		double n = 0.0;
		for (int j = 0; j < matrixB[i].length - commoditiesItems; j++) {
			n += matrixB[i][j];
		}
		return n;
	}

	/**
	 * Convert a Vector to an array
	 * 
	 * @param list
	 *            The vector to transform
	 * @return an array of equal size to the vector and the same elements
	 */
	private static double[] to_array(Vector list) {
		double[] array = new double[list.size()];
		for (int i = 0; i < array.length; i++)
			array[i] = ((Double) list.get(i)).doubleValue();
		return array;

	}

	/**
	 * Generate new columns given certain paths
	 * 
	 * @param paths
	 *            The shortest paths to generate columns from
	 * @param matrixA
	 *            The D-W matrix
	 * @param costs
	 *            The cost of each edge
	 * @param capac
	 *            The capacities of the edges
	 * @param objCoeff
	 *            The objective coefficients
	 * @param commod
	 *            the available commodities
	 */
	@SuppressWarnings({ "unchecked" })
	private static void generate_column(boolean[][] paths, Vector[] matrixA,
			Double[] costs, Double[] capac, Vector objCoeff, String[][] commod) {
		// For each commodity
		if (all_existent(path_names, matrixA, commod)) {
			for (int i = 0; i < paths.length; i++) {
				int index = get_first_empty_space(matrixA);
				// Check that the correct array index is returned and fill the
				// path

				if (index != -1 && existent(path_names[i])) {
					matrixA[index] = new Vector<Double>(paths[i].length
							+ paths.length);
					double sum = 0;
					// Generate a path for all edges
					for (int j = 0; j < paths[i].length; j++) {
						if (paths[i][j] == true) {
							double r = Double.parseDouble(commod[i][2]);
							double rc = Double.parseDouble(commod[i][2])
									* costs[j];
							matrixA[index].add(j, r);
							sum += rc;
						} else
							matrixA[index].add(j, 0.0);
					}
					objCoeff.add(sum);

					// Fill the constraint elements with 0

					boolean flag = true;
					// Fill in the commodities
					for (int l = matrixA[index].size(); l < costs.length
							+ paths.length - 1; l++)
						matrixA[index].add(l, 0.0);
					matrixA[index].add(costs.length + (index % paths.length),
							1.0);
					existing_path_names[i] = path_names[i];
				}
				if (path_names[i] != null)
					if (!mp.containsKey(path_names[i]))
						mp.put(path_names[i], index);
			}
		}

	}

	/**
	 * Check wether all generated paths already exist in the matrix. If they do,
	 * they won't be added and the convergence flag will switch to TRUE. This
	 * will signal the last iteration.
	 * 
	 * @param path_names2
	 *            The paths checked before added
	 * @param matrixA
	 *            the D-W matrix
	 * @param commod
	 *            the commodities
	 * @return a boolean true or false
	 */
	@SuppressWarnings("unchecked")
	private static boolean all_existent(String[] path_names2, Vector[] matrixA,
			String[][] commod) {
		boolean result = true;
		Vector tf = new Vector();
		for (int i = 0; i < get_first_place(path_names2); i++) {
			if (mp.containsKey(path_names2[i]))
				tf.add(true);
			else
				tf.add(false);
		}

		int iterat = 0;
		for (Iterator iterator = tf.iterator(); iterator.hasNext();) {
			Boolean object = (Boolean) iterator.next();
			if (object == true)
				iterat++;
		}
		if (iterat == tf.size() && iterat != 0) {
			result = false;
			converged = true;
		}
		return result;
	}

	private static String[] existing_path_names = new String[10];

	private static boolean existent(String path_names2) {
		boolean result = true;
		for (int i = 0; i < existing_path_names.length; i++) {
			if (mp.containsKey(path_names2))
				result = false;
		}

		return result;
	}

	private static int get_first_empty_space(Vector[] matrixA) {
		for (int i = 0; i < matrixA.length; i++) {
			if (matrixA[i] == null)
				return i;
		}
		return -1;
	}

	/**
	 * Retrieve the shortest path from a graph based on Dijkstra's algorithm
	 * 
	 * @param network
	 *            The DAG to derive a path from
	 * @param commod
	 *            The individual commodities to use as start and end nodes for
	 *            the paths
	 * @return
	 */
	private static boolean[][] solve_shortest_path(Graph network,
			String[][] commod) {
		boolean[][] paths = new boolean[commod.length][];
		for (int i = 0; i < commod.length; i++) {
			double cost = network.getShortestPath(commod[i][0], commod[i][1]);
			boolean[] used_edges = network.getUsedEdges();
			paths[i] = used_edges;
			path_names[get_first_place(path_names)] = network.getPath();
		}
		return paths;

	}

	/**
	 * Query the hashmap and return a String with the path that corresponds to
	 * the supplied index
	 * 
	 * @param mp2
	 *            the hashmap to look for the index
	 * @param i
	 *            the index to look for
	 * @return a String with the path name
	 */
	public static String getKeysByValue(
			HashMap<java.lang.String, java.lang.Integer> mp2, int i) {
		String keys = "";
		for (Entry<java.lang.String, java.lang.Integer> entry : mp2.entrySet()) {
			if (entry.getValue().equals(i)) {
				keys = (String) entry.getKey();
			}
		}
		return keys;
	}

}
