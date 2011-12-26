import java.text.*;
import lpsolve.*;

/** 
    LP solver class mark2 that calls lp_solve.
    @author Andreas Grothey (Java wrapper class)
    @version 10/02/11

 */

public class LP {

    private LpSolve lp;   // the current problem in lp_solve
    // sparse Problem data
    int n;
    int m;
    int nb_el;            // # of nonzeros in system Matrix
    double [] dels;       // Sparse elements of the matrix
    int [] rownbs;        // element row numbers
    int [] colpts;        // pointers to column starts
    int [] collen;        // length of columns
    double [] x;          // solution 
    double [] clo;        // col bounds
    double [] cup;        //
    double [] rlo;        // row bounds
    double [] rup;        //
    double [] dobj;       // objective coefficient
    double [] lam;        // vector of optimal multipliers
    double  f;            // optimal solution value
    double [][] A;        // placeholder for dense system matrix
                          // only used for pretty printing

    //int [] basis;         // optimal basis in EMSOL format

    int iprint;
    int ifail;
    boolean solved;       // indicates if the current problem has been solved
    boolean is_setup;     // indicates if problem has been passed to lp_solved
    //boolean warmstart;   // true if warmstart info exists

    /** Set up a new Linear Programming Problem. 
     * The problem has the form<br>
     * min c'x s.t. blo(1:n)<=x<=bup(1:n), blo(n+1:n+m)<=Ax<=bup(n+1:n+m)<br>
     * the system matrix A is given as sparse matrix
     * @param g       double[n]: cost vector
     * @param dels    double[n_nonzero]: nonzero elements of A
     * @param mcol    int[n_nonzero]: column indices of nonzeros of A
     * @param mrow    int[n_nonzero]: row indices of nonzeros of A
     * @param blo     double[n+m]: lower bounds array: first variable bounds 
     *                then constraint bounds 
     * @param bup     double[n+m]: upper bounds array: first variable bounds 
     *                then constraint bounds 
     * @exception IllegalArgumentException 
     *             thrown if array dimensions do not match
     */
    public LP(double[] g, int[] mcol, int[] mrow, double dels[], 
	      double[] blo, double[] bup) {
	int i;

	n = g.length;
	m = blo.length - n;
	nb_el = dels.length;
	if (mrow.length!=nb_el || mcol.length!=nb_el || bup.length!=n+m){
	    throw 
		new IllegalArgumentException("Inconsistent Array Dimensions");
	}
	if (m<1){
	    System.err.println("LP: Vector of lower bounds has wrong dimension:");
	    System.err.println("LP: dim blo[] = "+blo.length+".");
	    System.err.println("LP: Since n = dim g[] = "+g.length+" this implies m = "+m);
	    throw
		new IllegalArgumentException("Inconsistent Array Dimensions");

	}

	/* check mcol, mrow array for array indices in bound */

	int rix1, rix2, cix1, cix2, rixr, cixr;
	
	rix1 = 10*m;
	rix2 = -10*m;
	cix1 = 10*n;
	cix2 = -10*n;
	
	for(i=0;i<nb_el;i++){
	    if (mrow[i]>rix2) rix2 = mrow[i];
	    if (mrow[i]<rix1) rix1 = mrow[i];
	    if (mcol[i]>cix2) cix2 = mcol[i];
	    if (mcol[i]<cix1) cix1 = mcol[i];
	}
	if (rix1<0 || cix1<0) 
	    throw new IllegalArgumentException("Negative row/col index");
	if (rix2>=m || cix2>=n)  
	    throw new IllegalArgumentException("row/col index out of range");

	this.dobj = g;

	this.dels = new double[nb_el];
	this.rownbs = new int[nb_el];
	this.colpts = new int[n];
	this.collen = new int[n];

	int nxel = 0;
	for(int col=0;col<n;col++){
	    colpts[col] = nxel;
	    //scan for entries to this col in mcol
	    for(i=0;i<mcol.length;i++){
		if (mcol[i]==col){
		    this.dels[nxel] = dels[i];
		    rownbs[nxel] = mrow[i];
		    nxel++;
		}
	    }
	    collen[col] = nxel-colpts[col];
	}

	this.clo = new double[n];
	this.cup = new double[n];
	this.rlo = new double[m];
	this.rup = new double[m];

	for(i=0;i<n;i++){
	    this.clo[i] = blo[i];
	    this.cup[i] = bup[i];
	}
	for(i=0;i<m;i++){
	    this.rlo[i] = blo[n+i];
	    this.rup[i] = bup[n+i];
	}

	this.iprint = LpSolve.IMPORTANT;
	this.ifail = 0;
	//this.basis = new int[n+m];
	//this.warmstart = false;
	this.solved = false;
	this.is_setup = false;
	this.lam = new double[n+m];
	//this.basis = new int[n+m];
	this.x = new double[n];
    }

    /** Set up a new Linear Programming Problem. 
     * The problem has the form<br> 
     * min c'x s.t. blo(1:n)<=x<=bup(1:n), blo(n+1:n+m)<=Ax<=bup(n+1:n+m)
     * @param g       double[n]: cost vector 
     * @param A       double[m][n]: System matrix of system (array of rows)
     * @param blo     double[n+m]: lower bounds array: first variable bounds 
     *                    then constraint bounds 
     * @param bup     double[n+m]: upper bounds array: first variable bounds 
     *                    then constraint bounds 
     *
     * @exception IllegalArgumentException 
     *              thrown if array dimensions do not match
     */
    public LP(double[] g, double[][] A, double[] blo, double[] bup)
	throws IllegalArgumentException{
	int i, j, count;

	// A should be an array of rows, i.e. A[m][n]
	n = g.length;
	if (A[0].length!=n) {
	    throw 
		new IllegalArgumentException("Inconsistent Array Dimensions");
	}
	m = A.length;
	if (blo.length!=n+m || bup.length!=n+m){
	    throw 
		new IllegalArgumentException("Inconsistent Array Dimensions");
	}
	
	nb_el = 0;
	for(i=0;i<n;i++){
	    for(j=0;j<m;j++){
		if (Math.abs(A[j][i])>1e-10) nb_el++;
	    }
	}
	
	this.dels = new double[nb_el];
	this.rownbs = new int[nb_el];
	this.colpts = new int[n];
	this.collen = new int[n];

	count = 0;
	for(i=0;i<n;i++){
	    colpts[i] = count;
	    for(j=0;j<m;j++){
		if (Math.abs(A[j][i])>1e-10){
		    dels[count] = A[j][i];
		    rownbs[count] = j;
		    count++;
		}
	    }
	    collen[i] = count-colpts[i];
	}
	
	if (m<1){
	    System.err.println("LP: Vector of lower bounds has wrong dimension:");
	    System.err.println("LP: dim blo[] = "+blo.length+".");
	    System.err.println("LP: Since n = dim g[] = "+g.length+" this implies m = "+m);
	    throw
		new IllegalArgumentException("Inconsistent Array Dimensions");

	}

	this.clo = new double[n];
	this.cup = new double[n];
	this.rlo = new double[m];
	this.rup = new double[m];

	for(i=0;i<n;i++){
	    this.clo[i] = blo[i];
	    this.cup[i] = bup[i];
	}
	for(i=0;i<m;i++){
	    this.rlo[i] = blo[n+i];
	    this.rup[i] = bup[n+i];
	}

	this.dobj = g;
	this.iprint = LpSolve.IMPORTANT;
	this.ifail = 0;
	//this.basis = new int[n+m];
	//this.warmstart = false;
	this.solved = false;
	this.is_setup = false;
	this.lam = new double[n+m];
	this.x = new double[n];
	//this.basis = new int[n+m];
    } 

    /** Set up a new Linear Programming Problem. 
     * The problem has the form<br>
     * min c'x s.t. cl<=x<=cu, rl<=Ax<=ru<br>
     * the system matrix A is given as dense matrix
     * @param g       double[]: cost vector
     * @param A       double[][]: System matrix (Array of rows)
     * @param cl      double[]: lower bounds on variables
     * @param cu      double[]: upper bounds on variables
     * @param rl      double[]: lower bounds on constraints
     * @param ru      double[]: upper bounds on constraints
     * @param n       number of variables 
     *            (only first n columns of A and entries of g, cl, cu are used)
     * @param m       number of constraints
     *            (only first m rows of A and entries of rl, ru are used)
     * @exception IllegalArgumentException 
     *                       thrown if any array dimension is too small
     */
    public LP(double[] g, double[][] A, double[] cl, double[] cu, double[] rl,
	      double[] ru, int n, int m) throws IllegalArgumentException{
	int i, j, count;

	this.n = n;
	this.m = m;
	// check that all arrays have appropriate dimensions

	if (A[0].length<n || cl.length<n || cu.length<n || g.length<n) {
	    throw 
		new IllegalArgumentException("Some array column dimension <n");
	}
	if (A.length<m || rl.length<m || ru.length<m){
	    throw 
		new IllegalArgumentException("Some array row dimensions <m");
	}

	if (n<1 || m<1) {
	    throw 
		new IllegalArgumentException("Either n or m is zero");
	}

	// count number of nonzero elements in first nxm part of A
	nb_el = 0;
	for(i=0;i<n;i++){
	    for(j=0;j<m;j++){
		if (Math.abs(A[j][i])>1e-10) nb_el++;
	    }
	}
	
	// dimension sparse arrays

	this.dels = new double[nb_el];
	this.rownbs = new int[nb_el];
	this.colpts = new int[n];
	this.collen = new int[n];


	// copy nonzero elements from A to Sparse data format
	count = 0;
	for(i=0;i<n;i++){
	    colpts[i] = count;
	    for(j=0;j<m;j++){
		if (Math.abs(A[j][i])>1e-10){
		    dels[count] = A[j][i];
		    rownbs[count] = j;
		    count++;
		}
	    }
	    collen[i] = count-colpts[i];
	}

	// copy bounds into blo, bup arrays

	this.clo = cl;
	this.cup = cu;
	this.rlo = rl;
	this.rup = ru;

	this.dobj = g;
	this.iprint = LpSolve.IMPORTANT;
	this.ifail = 0;
	//this.basis = new int[n+m];
	//this.warmstart = false;
	this.solved = false;
	this.is_setup = false;
	this.lam = new double[n+m];
	this.x = new double[n];
	//this.basis = new int[n+m];
    } 

    /**
     * Sets new bounds for an existing LP
     * @param blo double[n+m]: lower bounds array: 
     *            first variable bounds then constraint bounds 
     * @param bup double[n+m]: upper bounds array: 
     *            first variable bounds then constraint bounds 
     * 
     * @exception IllegalArgumentException 
     *             thrown if array dimensions do not match
     */
    public void setBounds(double[] blo, double[] bup){
	int i;

	if (blo.length!=n+m || bup.length!=n+m){
	    throw 
		new IllegalArgumentException("Inconsistent Array Dimensions");
	}
	
       	for(i=0;i<n;i++){
	    this.clo[i] = blo[i];
	    this.cup[i] = bup[i];
	}
	for(i=0;i<m;i++){
	    this.rlo[i] = blo[n+i];
	    this.rup[i] = bup[n+i];
	}
	solved = false;
	is_setup = false;
    }

    /**
     * Sets a new objective for an existing LP
     * @param g       double[n]: cost vector
     * @exception IllegalArgumentException 
     *              thrown if array dimensions do not match
     */
    public void setObjective(double[] g){
	if (g.length!=n){
	    throw 
		new IllegalArgumentException("Inconsistent Array Dimensions");
	}
	
	for(int i=0;i<n;i++)
	    this.dobj[i] = g[i];

	solved = false;
	is_setup = false;
    }
    

    /**
     * Sets output level for solve
     * @param iprint  0=LpSolve.NEUTRAL  : none, 
     *                1=LpSolve.CRITICAL : critical errors
     *                2=LpSolve.SEVERE   : errors
     *                3=LpSolve.IMPORTANT: errors & warnings (default)
     *                4=LpSolve.NORMAL   : Status messages
     *                5=LpSolve.DETAILED : Detailed model information
     *                6=LpSolve.FULL     : Full debug info
     */
    public void setIprint(int iprint){
	this.iprint = iprint;
    }


    /**
     * Print out information about the LP solution on the screen
     * solve() needs to be called first
     */
    public void printSolution()
    {
	int i;
	if (!solved) {
	    System.out.println("Problem not solved yet");
	    return;
	}
	
	System.out.println("Ifail   = "+ifail);
	System.out.println("Opt Val = "+f);
	System.out.println("Solution:");
	for(i=0;i<n;i++)
	    System.out.println("x["+(i+1)+"] = "+x[i]);
	System.out.println("Multipliers:");
	for(i=0;i<n+m;i++)
	    System.out.println("lam["+(i+1)+"] = "+lam[i]);
	//System.out.println("Basis (EMSOL):");
	//for(i=0;i<n;i++)
	//    System.out.println("bs["+(i+1)+"] = "+basis[i]);
    }
    
  /**
   * prints the current LP data in a nice format (at least attempts to)
   */
  public void print()
    {
	DecimalFormat df = new DecimalFormat("###.###");
	System.out.println("--------------------------------- LP Data -------------------------------");

	System.out.println("#variables  : "+n);
	System.out.println("#constraints: "+m);
	System.out.println("");
	System.out.println("Cost:");
	for(int i=0;i<n;i++){
	    System.out.print(widthPrint(df.format(dobj[i]),8)+" ");
	}
	System.out.println("");
	// create dense data
	this.A = new double[m][n];
	for(int i=0;i<n;i++){
	    for(int j=colpts[i];j<colpts[i]+collen[i];j++)
		A[rownbs[j]][i] = dels[j];
	}
	
	System.out.println("");
	System.out.println("System Matrix:");
	for(int i=0;i<m;i++){
	    for(int j=0;j<n;j++){
		System.out.print(widthPrint(df.format(A[i][j]),8)+" ");
	    }
	    System.out.println("");
	}

	System.out.println("");
	System.out.println("Upper and Lower bounds on variables (columns):");
	for(int i=0;i<n;i++){
	    System.out.println(i+": "+widthPrint(df.format(clo[i]),8)+" "+widthPrint(df.format(cup[i]),8));
	}
	System.out.println("");

	System.out.println("Upper and Lower bounds on constraints (rows):");
	for(int i=0;i<m;i++){
	    System.out.println(i+": "+widthPrint(df.format(rlo[i]),8)+" "+widthPrint(df.format(rup[i]),8));
	}
	System.out.println("----------------------------- End of LP Data ----------------------------");

    }

    /**
     * returns a double[n] containing the solution vector x
     * @return the solution vector x
     */
    public double [] getSolution() throws Exception{
	if (!solved) solve();
	return x;
    }

    /**
     * returns a double[n+m] containing variable and constraint multipliers
     *  @return the multiplier vector: 
     *            first n locations are multipliers on variable bounds, 
     *            next m are multipliers on constraints
     */
    public double [] getMultipliers() throws Exception{
	if (!solved) solve();
      return lam;
    }

    /**
     * returns information on the solution status of the LP
     *  @return ifail: 0=OK, 
     *                 1=not converged, 
     *                 2=infeasible, 
     *                 3=unbounded, 
     *               >=4 other failure
     */
    public int getIfail(){
	if (!solved) return 99; 
	return this.ifail;
    }

    /**
     * returns the optimal value g'x
     *  @return f = g'x
     */
    public double getValue() throws Exception{
	if (!solved) solve();
	return this.f;
    }
    
    /**
     * returns basis information
     * returns an int[n+m] containing information on optimal basis
     * @return int[n+m] basis information
     */
    //public int [] getBasis(){
    //if (!solved) solve();
    //return basis;
    //}

    /**
     * sets the starting basis
     * @param bas int[n+m] containing basis information in EMSOL format
     */
    //public void setBasis(int [] bas){
    //if (bas.length != n+m) {
    //throw 
    //new IllegalArgumentException("Inconsistent Array Dimensions");
    //}
    //this.basis = bas;
    //}
    

    /**
     * Test method.
     *  defines a small 1x2 LP solves it and prints the solution
     *
     *  min -x_1 -x_2 
     *  s.t. 0 <= 0.5*x_1 + 2*x_2 <= 1
     *       0 <= -2*x_1 -0.5*x_2 <= 1
     *       0 <= x_1, x_2 <= 2 
     */     
    public static void main(String[] args) throws Exception{
	
	int n = 2;
	int m = 1;
	
	double[] g = new double[]{-1.0, -1.0};
	double[] blo = new double[]{0.0, 0.0, 0.0, 0.0};
//	double[] blo = new double[]{0.0, 0.0, 0.0};
//	double[] bup = new double[]{2.0, 2.0, 3.0};
	double[] bup = new double[]{2.0, 2.0, 1.0, 1.0};
	double[][] A   = new double[][]{
	    new double[]{0.5, 2.0},
	    new double[]{-2.0, -0.5}};
//	    new double[]{1.0, 1.0}};

	LP jlp = new LP(g, A, blo, bup);
	jlp.print();
	jlp.solve();
	jlp.printSolution();
	jlp.writeMPS("test.mps");
    }

    private String widthPrint(String s, int d){
	StringBuffer sb = new StringBuffer("");
	for(int i=0;i<d-s.length();i++) sb.append(" ");
	sb.append(s);
	return sb.toString();
    }


    /** 
     * Communicates the currently defined problem to lp_solve.
     */
    private void setupProblem() throws Exception
    {
	// construct the problem column by column
	lp = LpSolve.makeLp(m, n);
	
	// set output level
	lp.setVerbose(iprint);

	double[] col;
	int i, j;
	
	for (i=0;i<n;i++){
	  col = new double[m+1];

	    // create next column as dense vector
	    for(j=colpts[i];j<colpts[i]+collen[i];j++){
		col[rownbs[j]+1] = dels[j];
	    }
	    
	    // add to LP and set column bounds
	    lp.setColumn(i+1, col);
	    lp.setBounds(i+1,clo[i],cup[i]);
	    lp.setObj(i+1,dobj[i]);
	}
	    
	for(j=0;j<m;j++){
	    if (rlo[j]>-1.e+20){
		// lower bound present
		if (rup[j]<1.e+20){
		    // upper bound as well
		    if (Math.abs(rup[j]-rlo[j])<1.e-6){
			// equality constraint
			lp.setConstrType(j+1,LpSolve.EQ);
			lp.setRh(j+1, rlo[j]);
		    }else{
			// range constraint
			lp.setConstrType(j+1,LpSolve.GE);//???
			lp.setRh(j+1, rlo[j]);
			lp.setRhRange(j+1, rup[j]-rlo[j]);
		    }
		}else{
		    // only lower bound
		    lp.setConstrType(j+1,LpSolve.GE);
		    lp.setRh(j+1, rlo[j]);
		}
	    }else{
		// no lower bound
		if (rup[j]<1e+20){
		    // only upper bound
		    lp.setConstrType(j+1,LpSolve.LE);
		    lp.setRh(j+1, rup[j]);
		}else{
		    // free variable
		    lp.setConstrType(j+1,LpSolve.FR);
		}
	    }
	}

	//lp.printLp();
	is_setup = true;
    }

    /** 
     * Sets up the LP in lp_solve and solves it
     */
    public void solve() throws Exception
    {
	if (!is_setup) setupProblem();
	ifail = lp.solve();
	//ifail = lp.getStatus();
	System.out.println(lp.getStatustext(ifail));
	lp.getVariables(x);
	// NOTE: duals are returned the other way round to EMSOL/Filter
	//       Constraints first then variables!
	double[] lamtmp = new double[n+m+1];
	lp.getDualSolution(lamtmp);
	for(int i=0;i<n;i++)
	    lam[i] = lamtmp[i+m+1];
	for(int i=0;i<m;i++)
	    lam[n+i] = lamtmp[i+1];
	f = lp.getObjective();
	System.out.println("lp_solve: ifail="+ifail+", f="+f+
			   ", LP iters:"+lp.getTotalIter());
	solved = true;
    }


  /**
   * Write the current model in MPS format to the given file
   * @param filename    The name of the MPS file to save in
   */
    public void writeMPS(String filename) throws Exception
    {
	if (!is_setup) setupProblem();
	lp.writeMps(filename);
    }

    /**
     * Return the number of iterations for the LP solver
     * @return number of iterations.
     */
public Long getIters() {
	// TODO Auto-generated method stub
	return lp.getTotalIter();
}

}








