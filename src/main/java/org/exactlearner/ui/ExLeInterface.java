package org.exactlearner.ui;

import java.awt.EventQueue;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;

import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSlider;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.border.EmptyBorder;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import org.coode.owlapi.manchesterowlsyntax.ManchesterOWLSyntaxEditorParser;
import org.coode.owlapi.manchesterowlsyntax.ManchesterOWLSyntaxOntologyFormat;
import org.exactlearner.console.consoleLearner;
import org.exactlearner.engine.ELEngine;
import org.exactlearner.learner.ELLearner;
import org.exactlearner.oracle.ELOracle;
import org.exactlearner.tree.ELTree;
import org.exactlearner.utils.Metrics;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.expression.OWLEntityChecker;
import org.semanticweb.owlapi.expression.ShortFormEntityChecker;
import org.semanticweb.owlapi.io.OWLObjectRenderer;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyFormat;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.RemoveAxiom;
import org.semanticweb.owlapi.util.BidirectionalShortFormProviderAdapter;
import org.semanticweb.owlapi.util.SimpleShortFormProvider;

import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxOWLObjectRendererImpl;

public class ExLeInterface extends JFrame {

	// ****************** START FRAME SPECIFIC VARIABLES ******************
	
	public JPanel contentPane;
	public JButton membershipButton;
	public JTextArea hypothesisArea;
	public JButton learnButton;
	public JLabel answerLabel;
	public JLabel totalQueries;
	public JLabel membQueries;
	public JLabel equivQueries;
	public JButton restartButton;
	public JButton helpButton;
	public JLabel percentageSlider;
	public JSlider slider;
	public JLabel oracleDifficulty;
	public JCheckBox decompLeft;
	public JCheckBox branchLeft;
	public JCheckBox unsatLeft;
	public JCheckBox decompRight;
	public JCheckBox mergeRight;
	public JCheckBox satRight;
	
	// ****************** END FRAME SPECIFIC VARIABLES ******************

	public static double SATURATION_BOUND = 0d;
	public static double MERGE_BOUND = 0d;
	public static double BRANCH_BOUND = 0d;
	public static double UNSATURATE_BOUND = 0d;
	public static double COMPOSE_LEFT_BOUND = 0d;
	public static double COMPOSE_RIGHT_BOUND = 0d;

	public String filePath;
	public File targetFile;
	public File newFile;
	public ShowVocabulary showThem = null;
	public HelpInterface helpThem = null;
	public HistoryInterface historyThem = null;
	public Vector<Object[]> historyData = new Vector<Object[]>();
	// #########################################################

	// ############# OWL variables Start ######################

	public static OWLOntologyManager myManager = OWLManager.createOWLOntologyManager();
	public static OWLObjectRenderer myRenderer = new ManchesterOWLSyntaxOWLObjectRendererImpl();
	public static Metrics myMetrics = new Metrics(myRenderer);

	public Set<OWLAxiom> axiomsT = null;
	public Set<OWLAxiom> axiomsTtmp = null;

	public String ontologyFolder = null;
	public String ontologyName = null;
	public File hypoFile = null;

	public String ontologyFolderH = null;

	public OWLSubClassOfAxiom lastCE = null;
	public OWLClassExpression lastExpression = null;
	public OWLClass lastName = null;
	public OWLOntology targetOntology = null;
	public OWLOntology hypothesisOntology = null;

	public ELEngine elQueryEngineForT = null;
	public ELEngine elQueryEngineForH = null;

	public ELLearner elLearner = null;
	public ELOracle elOracle = null;

	ArrayList<String> concepts;

	ArrayList<String> roles;
	
	// ############# OWL variables End ######################

	// #########################################################

	// ############# Oracle and Learner Skills Start ######################

	public boolean oracleSaturate = false;
	public boolean oracleMerge = false;
	public boolean oracleBranch = false;
	public boolean oracleUnsaturate = false;
	public boolean oracleLeftCompose = false;
	public boolean oracleRightCompose = false;

	public boolean learnerSat;
	public boolean learnerMerge;
	public boolean learnerDecompL;
	public boolean learnerUnsat;
	public boolean learnerBranch;
	public boolean learnerDecompR;
	static consoleLearner maker;
	private JScrollPane scrollPane;

	class EquivalentException extends Exception {

		EquivalentException(String no_more_counterexamples) {
			super(no_more_counterexamples);
		}
	}

	// ############# Oracle and Learner Skills End ######################

	/**
	 * Launch the application.
	 */

	public static void main(String[] args) {
		EventQueue.invokeLater(new Runnable() {
			public void run() {
				try {
					ExLeInterface frame = new ExLeInterface(
							new File("src/main/resources/ontologies/SMALL/university.owl"));
					frame.setVisible(true);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		});
	}

	public OWLClassExpression parseClassExpression(String str) {
		ManchesterOWLSyntaxEditorParser parser = new ManchesterOWLSyntaxEditorParser(
				targetOntology.getOWLOntologyManager().getOWLDataFactory(), str);

		parser.setDefaultOntology(targetOntology);
		OWLEntityChecker entityChecker = new ShortFormEntityChecker(new BidirectionalShortFormProviderAdapter(myManager,
				targetOntology.getImportsClosure(), new SimpleShortFormProvider()));
		parser.setOWLEntityChecker(entityChecker);
		// Do the actual parsing
		try {
			return parser.parseClassExpression();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			System.out.println("The concept " + str + " is not in this Ontology.");
			JOptionPane.showMessageDialog(null, "The concept " + str + "  is not in this Ontology!", "Alert",
					JOptionPane.INFORMATION_MESSAGE);

		}
		return null;
	}

	public void initializeVariables() {
		filePath = this.targetFile.getPath();

		try {
			// load targetOntology
			setupOntologies();

			elQueryEngineForT = new ELEngine(targetOntology);
			elQueryEngineForH = new ELEngine(hypothesisOntology);

			elLearner = new ELLearner(elQueryEngineForT, elQueryEngineForH, myMetrics);
			elOracle = new ELOracle(elQueryEngineForT, elQueryEngineForH);

		} catch (Throwable e) {
			e.printStackTrace();
			System.out.println("error in initializeVariables ----- " + e);
		}
	}

	/**
	 * Create the frame.
	 */

	public ExLeInterface(File ontology) {
		this.targetFile = ontology;
		System.out.println("Target file is: " + targetFile);
		System.out.println("Ontology path is: " + ontology.getPath());
		initializeVariables();
		setResizable(false);
		setTitle("ExactLearner - An Ontology Learning Tool");
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		setBounds(100, 100, 751, 457);
		contentPane = new JPanel();
		contentPane.setBorder(new EmptyBorder(5, 5, 5, 5));
		setContentPane(contentPane);
		contentPane.setLayout(null);

		helpButton = new JButton("Help");
		helpButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				if (helpThem != null) {
					helpThem.dispose();
				}
				helpThem = new HelpInterface();
				helpThem.setVisible(true);
			}
		});
		helpButton.setBounds(615, 11, 120, 23);
		contentPane.add(helpButton);

		JLabel lblNewLabel_2 = new JLabel("Hypothesis");
		lblNewLabel_2.setBounds(10, 33, 191, 14);
		contentPane.add(lblNewLabel_2);

		learnButton = new JButton("Learn ontology");
		learnButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent arg0) {
				
				setLearnerSkills();
				setOracleSkills(slider.getValue() / 100 + "");

				try {

					long timeStart = System.currentTimeMillis();
					runLearner(elQueryEngineForT, elQueryEngineForH);
					long timeEnd = System.currentTimeMillis();
					saveOWLFile(hypothesisOntology, hypoFile);

					elQueryEngineForH.disposeOfReasoner();
					elQueryEngineForT.disposeOfReasoner();
					myManager.removeOntology(hypothesisOntology);
					myManager.removeOntology(targetOntology);
					System.out.println("Ontology successfully learned!");
					System.out.println("Time: " + (timeEnd - timeStart) + "ms");
					System.out.println(
							"Target TBox logical axioms: " + axiomsT.size());
					System.out.println("Size of T: " + myMetrics.sizeOfCIT(targetOntology.getLogicalAxioms()));
					System.out.println("Hypothesis TBox logical axioms: " + hypothesisOntology.getLogicalAxiomCount());
					System.out.println("Size of H: " + myMetrics.sizeOfCIT(hypothesisOntology.getLogicalAxioms()));
					System.out.println();
					/*System.out.println(elOracle.getNumberLeftComposition());
					System.out.println(elOracle.getNumberMerging());
					System.out.println(elOracle.getNumberSaturations());
					System.out.println(elOracle.getNumberRightComposition());
					System.out.println(elOracle.getNumberBranching());
					System.out.println(elOracle.getNumberUnsaturations());
					System.out.println();

					System.out.println(elLearner.getNumberLeftDecomposition()); 
					System.out.println(elLearner.getNumberBranching());
					System.out.println(elLearner.getNumberUnsaturations());
					System.out.println(elLearner.getNumberRightDecomposition());
					System.out.println(elLearner.getNumberMerging());
					System.out.println(elLearner.getNumberSaturations());*/
					System.out.println();

					hypothesisArea.setText(showHypothesis());
					learnButton.setEnabled(false);
					elQueryEngineForH = null;
					elQueryEngineForT = null;
					myManager = OWLManager.createOWLOntologyManager();
					myRenderer = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					myMetrics = new Metrics(myRenderer);
					elLearner = null;
					elOracle = null; 
					learnButton.setEnabled(false);
				} catch (Exception e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (Throwable e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		});
		learnButton.setBounds(438, 260, 264, 42);
		contentPane.add(learnButton);

		answerLabel = new JLabel("Ontology learned: ---");
		answerLabel.setBounds(10, 317, 154, 14);
		contentPane.add(answerLabel);

		restartButton = new JButton("Restart");
		restartButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				
				int n = JOptionPane.showConfirmDialog(null, "Would you like to restart the current ontology?", "Alert!",JOptionPane.YES_NO_OPTION);
				if(n == 0){
					if (historyThem != null) {
						historyThem.dispose();
					}
					if (showThem != null) {

						showThem.dispose();
					}
					if (helpThem != null) {

						helpThem.dispose();
					}  
					hypoFile.delete();
		          		  newFile.delete();
		          		  historyData.clear();  
		           		 concepts.clear();
		           		 roles.clear(); 
					(new ExLeInterface(targetFile)).setVisible(true);
					dispose();
					/*
					hypothesisArea.setText("");
					learnButton.setEnabled(true);
					answerLabel.setText("Ontology learned: --");
					totalQueries.setText("Total number of queries: -- ");
					membQueries.setText("No. of entailment queries: -- ");
					equivQueries.setText("No. of equivalence queries: -- ");
					initializeVariables();*/
				}
				else {
					elQueryEngineForT = null;
					elQueryEngineForH = null;

					elLearner = null;
					elOracle = null;
					if (historyThem != null) {
						historyThem.dispose();
					}
					if (showThem != null) {

						showThem.dispose();
					}
					if (helpThem != null) {

						helpThem.dispose();
					}    
					(new StartUILearner()).setVisible(true); 
					dispose();
					 
				}
			}
		});
		restartButton.setBounds(582, 394, 120, 23);
		contentPane.add(restartButton);

		totalQueries = new JLabel("Total number of queries: --");
		totalQueries.setBounds(10, 342, 255, 14);
		contentPane.add(totalQueries);

		membQueries = new JLabel("No. of entailment queries: --");
		membQueries.setBounds(10, 367, 255, 14);
		contentPane.add(membQueries);

		equivQueries = new JLabel("No. of equivalence queries: --");
		equivQueries.setBounds(10, 394, 255, 14);
		contentPane.add(equivQueries);

		slider = new JSlider();
		slider.addChangeListener(new ChangeListener() {
			public void stateChanged(ChangeEvent arg0) {
				percentageSlider.setText(slider.getValue() + "%");
				System.out.println("Oracle skills chance of activation at: " + slider.getValue() + "%.");
				if (slider.getValue() > 33 && slider.getValue() < 67)
					oracleDifficulty.setText("Oracle difficulty: Medium");
				if (slider.getValue() <= 33 && slider.getValue() > 0)
					oracleDifficulty.setText("Oracle difficulty: Easy");
				if (slider.getValue() >= 67)
					oracleDifficulty.setText("Oracle difficulty: Hard");
				if (slider.getValue() == 0)
					oracleDifficulty.setText("Oracle difficulty: Off");
			}
		});
		slider.setBounds(438, 58, 200, 26);
		contentPane.add(slider);

		oracleDifficulty = new JLabel("Oracle difficulty: Medium");
		oracleDifficulty.setBounds(436, 33, 216, 14);
		contentPane.add(oracleDifficulty);

		percentageSlider = new JLabel("50%");
		percentageSlider.setBounds(648, 58, 46, 14);
		contentPane.add(percentageSlider);

		scrollPane = new JScrollPane();
		scrollPane.setBounds(12, 56, 408, 193);
		contentPane.add(scrollPane);

		hypothesisArea = new JTextArea();
		scrollPane.setViewportView(hypothesisArea);
		hypothesisArea.setEditable(false);

		decompLeft = new JCheckBox("Decompose left");
		decompLeft.setBounds(426, 142, 146, 23);
		contentPane.add(decompLeft);

		branchLeft = new JCheckBox("Branch left");
		branchLeft.setBounds(426, 168, 146, 23);
		contentPane.add(branchLeft);
		unsatLeft = new JCheckBox("Desaturate left");
		unsatLeft.setBounds(426, 194, 146, 23);
		contentPane.add(unsatLeft);
		decompRight = new JCheckBox("Decompose right");
		decompRight.setBounds(582, 142, 146, 23);
		contentPane.add(decompRight);

		mergeRight = new JCheckBox("Merge right");
		mergeRight.setBounds(582, 168, 146, 23);
		contentPane.add(mergeRight);

		satRight = new JCheckBox("Saturate right");
		satRight.setBounds(582, 194, 153, 23);
		contentPane.add(satRight);

		JLabel lblNewLabel = new JLabel("Learner skills");
		lblNewLabel.setBounds(438, 121, 264, 14);
		contentPane.add(lblNewLabel);
	}

	public void equivalenceCheck() {

		try {
			// precomputation(elQueryEngineForT, elQueryEngineForH);

			if (elQueryEngineForH.entailed(targetOntology.getTBoxAxioms(true))) {
				System.out.println("yes");
				victory();
			} else {
				OWLSubClassOfAxiom counterexample = null;
				try {
					counterexample = getCounterExample(elQueryEngineForT, elQueryEngineForH);

				} catch (Exception e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
				addHypothesis(counterexample);
				hypothesisArea.setText(showHypothesis());
				ELTree left = new ELTree(counterexample.getSubClass());
				ELTree right = new ELTree(counterexample.getSuperClass());
				ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();

				answerLabel.setText("Answer: No");

				myMetrics.setEquivCount(myMetrics.getEquivCount() + 1);
				updateQueries();
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public String showHypothesis() throws Exception {

		Set<OWLAxiom> axiomsInH = hypothesisOntology.getAxioms();
		String hypoInManchester = "";
		ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
		for (OWLAxiom axiom : axiomsInH) {
			hypoInManchester = hypoInManchester + rendering.render(axiom) + "\n";
		}
		return hypoInManchester;
	}

	public void membershipQuery(String conc1, String conc2) throws Exception {

		String entailQ = conc1 + " subclass of " + conc2;
		String answer = "";
		OWLClassExpression left = parseClassExpression(conc1);
		OWLClassExpression right = parseClassExpression(conc2);
		OWLAxiom axe = elQueryEngineForT.getSubClassAxiom(left, right);
		if (elQueryEngineForT.entailed(axe)) {
			// System.out.println("Was entailed");
			answer = "Yes.";
			addHypothesis(axe);
			answerLabel.setText("Answer: Yes");
			myMetrics.setMembCount(myMetrics.getMembCount() + 1);
			hypothesisArea.setText(showHypothesis());
			updateQueries();
		} else {
			// System.out.println("not entailed");
			answer = "No.";
			myMetrics.setMembCount(myMetrics.getMembCount() + 1);
			answerLabel.setText("Answer: No");
		}
		Object[] historyStuff = { myMetrics.getMembCount(), entailQ, answer };
		historyData.addElement(historyStuff);

	}

	private OWLOntology MinHypothesis(OWLOntology hypoOntology, OWLAxiom addedAxiom) {
		Set<OWLAxiom> tmpaxiomsH = hypoOntology.getAxioms();
		Iterator<OWLAxiom> ineratorMinH = tmpaxiomsH.iterator();
		Set<OWLAxiom> checkedAxiomsSet = new HashSet<OWLAxiom>();
		String removedstring = "";
		Boolean flag = false;
		ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();

		if (tmpaxiomsH.size() > 1) {
			while (ineratorMinH.hasNext()) {
				OWLAxiom checkedAxiom = ineratorMinH.next();
				if (!checkedAxiomsSet.contains(checkedAxiom)) {
					checkedAxiomsSet.add(checkedAxiom);

					OWLOntology tmpOntologyH = hypoOntology;
					RemoveAxiom removedAxiom = new RemoveAxiom(tmpOntologyH, checkedAxiom);
					myManager.applyChange(removedAxiom);

					ELEngine tmpELQueryEngine = new ELEngine(hypothesisOntology);
					Boolean queryAns = tmpELQueryEngine.entailed(checkedAxiom);

					if (queryAns) {
						RemoveAxiom removedAxiomFromH = new RemoveAxiom(hypoOntology, checkedAxiom);
						myManager.applyChange(removedAxiomFromH);
						removedstring = "\t[" + rendering.render(checkedAxiom) + "]\n";
						if (checkedAxiom.equals(addedAxiom)) {
							flag = true;
						}
					} else {
						AddAxiom addAxiomtoH = new AddAxiom(hypoOntology, checkedAxiom);
						myManager.applyChange(addAxiomtoH);

					}
				}
			}
			if (!removedstring.equals("")) {
				String message;
				if (flag) {
					message = "The axiom [" + rendering.render(addedAxiom) + "] will not be added to hypothesis\n"
							+ "since it can be replaced by some axioms that have existed in the hypothesis.";
				} else {
					message = "The following axiom will be removed after adding [" + rendering.render(addedAxiom)
							+ "]:\n" + removedstring;
				}
				JOptionPane.showMessageDialog(null, message, "Alert", JOptionPane.INFORMATION_MESSAGE);
			}
		}
		return hypoOntology;
	}

	public void updateQueries() {
		totalQueries.setText("Total number of queries: " + (myMetrics.getEquivCount() + myMetrics.getMembCount()));
		membQueries.setText("No. of entailment queries: " + myMetrics.getMembCount());
		equivQueries.setText("No. of equivalence queries: " + myMetrics.getEquivCount());
	}

	public void setOracleSkills(String val) {
		if (!val.equals("0")) {
			oracleMerge = true;
			MERGE_BOUND = Double.parseDouble(val);
		}
		if (!val.equals("0")) {
			oracleSaturate = true;
			SATURATION_BOUND = Double.parseDouble(val);
		}
		if (!val.equals("0")) {
			oracleBranch = true;
			BRANCH_BOUND = Double.parseDouble(val);
		}
		if (!val.equals("0")) {
			oracleUnsaturate = true;
			UNSATURATE_BOUND = Double.parseDouble(val);
		}
		if (!val.equals("0")) {
			oracleLeftCompose = true;
			COMPOSE_LEFT_BOUND = Double.parseDouble(val);
		}
		if (!val.equals("0")) {
			oracleRightCompose = true;
			COMPOSE_RIGHT_BOUND = Double.parseDouble(val);
		}

	}

	public void setLearnerSkills() {

		learnerDecompL = decompLeft.isSelected();

		learnerBranch = branchLeft.isSelected();

		learnerUnsat = unsatLeft.isSelected();

		learnerDecompR = decompRight.isSelected();

		learnerMerge = mergeRight.isSelected();

		learnerSat = satRight.isSelected();

	}

	public void runLearner(ELEngine elQueryEngineForT, ELEngine elQueryEngineForH) throws Throwable {
		// computes inclusions of the form A implies B
		precomputation(elQueryEngineForT, elQueryEngineForH);

		try {
			while (true) {
				myMetrics.setEquivCount(myMetrics.getEquivCount() + 1);

				lastCE = getCounterExample(elQueryEngineForT, elQueryEngineForH);

				OWLSubClassOfAxiom counterexample = lastCE;
				OWLClassExpression left = counterexample.getSubClass();
				OWLClassExpression right = counterexample.getSuperClass();
				lastCE = elLearner.decompose(left, right);

				if (canTransformELrhs()) {
					lastCE = computeEssentialRightCounterexample();
					Set<OWLSubClassOfAxiom> myAxiomSet = elQueryEngineForH.getOntology()
							.getSubClassAxiomsForSubClass(lastName);
					for (OWLSubClassOfAxiom ax : myAxiomSet) {
						if (ax.getSubClass().getClassExpressionType() == ClassExpressionType.OWL_CLASS) {
							OWLClass cl = (OWLClass) ax.getSubClass();
							if (cl.equals(lastName)) {
								Set<OWLClassExpression> mySet = new HashSet<>();
								mySet.addAll(ax.getSuperClass().asConjunctSet());
								mySet.addAll(lastExpression.asConjunctSet());
								lastCE = elQueryEngineForT.getSubClassAxiom(lastName,
										elQueryEngineForT.getOWLObjectIntersectionOf(mySet));
							}
						}
					}

					lastCE = computeEssentialRightCounterexample();
					addHypothesis(lastCE);
				} else if (canTransformELlhs()) {
					lastCE = computeEssentialLeftCounterexample();
					addHypothesis(lastCE);
				} else {
					addHypothesis(lastCE);
					System.out.println("Not an EL Terminology:" + lastCE.toString());

				}

			}
		} catch (EquivalentException e) {
			// nothing to do: no counterexample has been found
		}

		victory();
		lastCE = null;

	}

	public void addHypothesis(OWLAxiom addedAxiom) throws Exception {

		AddAxiom newAxiomInH = new AddAxiom(hypothesisOntology, addedAxiom);
		myManager.applyChange(newAxiomInH);

		saveOWLFile(hypothesisOntology, hypoFile);

		// minimize hypothesis
		hypothesisOntology = MinHypothesis(hypothesisOntology, addedAxiom);
		saveOWLFile(hypothesisOntology, hypoFile);

		myManager.addAxiom(hypothesisOntology, addedAxiom);

	}

	public void saveOWLFile(OWLOntology ontology, File file) throws Exception {

		minimiseHypothesis();
		OWLOntologyFormat format = myManager.getOntologyFormat(ontology);
		ManchesterOWLSyntaxOntologyFormat manSyntaxFormat = new ManchesterOWLSyntaxOntologyFormat();
		if (format.isPrefixOWLOntologyFormat()) {
			// need to remove prefixes
			manSyntaxFormat.clearPrefixes();
		}

		myManager.saveOntology(ontology, manSyntaxFormat, IRI.create(file.toURI()));
	}

	public void minimiseHypothesis() {

		Set<OWLAxiom> tmpaxiomsH = elQueryEngineForH.getOntology().getAxioms();
		Iterator<OWLAxiom> ineratorMinH = tmpaxiomsH.iterator();
		Set<OWLAxiom> checkedAxiomsSet = new HashSet<>();

		if (tmpaxiomsH.size() > 1) {
			while (ineratorMinH.hasNext()) {
				OWLAxiom checkedAxiom = ineratorMinH.next();

				if (!checkedAxiomsSet.contains(checkedAxiom)) {
					checkedAxiomsSet.add(checkedAxiom);
					if (checkedAxiom.isOfType(AxiomType.SUBCLASS_OF)) {
						OWLSubClassOfAxiom axiom = (OWLSubClassOfAxiom) checkedAxiom;
						OWLClassExpression left = axiom.getSubClass();
						OWLClassExpression right = axiom.getSuperClass();

						if (elQueryEngineForH.entailed(elQueryEngineForH.getSubClassAxiom(right, left))) {
							RemoveAxiom removedAxiom = new RemoveAxiom(elQueryEngineForH.getOntology(), checkedAxiom);
							elQueryEngineForH.applyChange(removedAxiom);
							AddAxiom addAxiomtoH = new AddAxiom(hypothesisOntology,
									elQueryEngineForH.getOWLEquivalentClassesAxiom(left, right));
							elQueryEngineForH.applyChange(addAxiomtoH);
						}
					}
					RemoveAxiom removedAxiom = new RemoveAxiom(elQueryEngineForH.getOntology(), checkedAxiom);
					elQueryEngineForH.applyChange(removedAxiom);

					if (!elQueryEngineForH.entailed(checkedAxiom)) {
						// put it back
						AddAxiom addAxiomtoH = new AddAxiom(hypothesisOntology, checkedAxiom);
						elQueryEngineForH.applyChange(addAxiomtoH);
					}
				}

			}
		}

	}

	public Boolean canTransformELrhs() {

		OWLSubClassOfAxiom counterexample = lastCE;
		OWLClassExpression left = counterexample.getSubClass();
		OWLClassExpression right = counterexample.getSuperClass();
		for (OWLClass cl1 : left.getClassesInSignature()) {
			if (elOracle.isCounterExample(cl1, right)) {
				lastCE = elQueryEngineForT.getSubClassAxiom(cl1, right);
				lastExpression = right;
				lastName = cl1;
				return true;
			}
		}
		return false;
	}

	public Boolean canTransformELlhs() {
		OWLSubClassOfAxiom counterexample = lastCE;
		OWLClassExpression left = counterexample.getSubClass();
		OWLClassExpression right = counterexample.getSuperClass();
		for (OWLClass cl1 : right.getClassesInSignature()) {
			if (elOracle.isCounterExample(left, cl1)) {
				lastCE = elQueryEngineForT.getSubClassAxiom(left, cl1);
				lastExpression = left;
				lastName = cl1;
				return true;
			}
		}
		return false;
	}

	public OWLSubClassOfAxiom computeEssentialLeftCounterexample() throws Exception {
		OWLSubClassOfAxiom axiom = lastCE;

		lastExpression = axiom.getSubClass();
		lastName = (OWLClass) axiom.getSuperClass();

		if (learnerDecompL) {
			axiom = elLearner.decomposeLeft(lastExpression, lastName);

			lastExpression = axiom.getSubClass();
			lastName = (OWLClass) axiom.getSuperClass();
		}

		if (learnerBranch) {
			axiom = elLearner.branchLeft(lastExpression, lastName);
			lastExpression = axiom.getSubClass();
			lastName = (OWLClass) axiom.getSuperClass();
		}

		if (learnerUnsat) {
			axiom = elLearner.unsaturateLeft(lastExpression, lastName);
		}

		return axiom;
	}

	public OWLSubClassOfAxiom computeEssentialRightCounterexample() throws Exception {
		OWLSubClassOfAxiom axiom = lastCE;

		lastName = (OWLClass) axiom.getSubClass();
		lastExpression = axiom.getSuperClass();

		if (learnerDecompR) {
			axiom = elLearner.decomposeRight(lastName, lastExpression);

			lastName = (OWLClass) axiom.getSubClass();
			lastExpression = axiom.getSuperClass();
		}

		if (learnerSat) {
			axiom = elLearner.saturateRight(lastName, lastExpression);
			lastName = (OWLClass) axiom.getSubClass();
			lastExpression = axiom.getSuperClass();
		}

		if (learnerMerge) {
			axiom = elLearner.mergeRight(lastName, lastExpression);

		}

		return axiom;
	}

	public void victory() throws Exception {

		// sanity check
		if (!elQueryEngineForH.entailed(axiomsT)) {
			throw new Exception("something went horribly wrong!!!!");
		}

		System.out.println("\nOntology learned successfully!");
		System.out.println("You dun did it!!!");
		axiomsT = new HashSet<>();
		for (OWLAxiom axe : targetOntology.getAxioms())
			if (!axe.toString().contains("Thing") && axe.isOfType(AxiomType.SUBCLASS_OF)
					|| axe.isOfType(AxiomType.EQUIVALENT_CLASSES))
				axiomsT.add(axe);
		answerLabel.setText("Ontology learned: Yes");
		updateQueries();
		updateQueries();
		
		JOptionPane.showMessageDialog(null, "You have learned the ontology!!!", "Success!",
				JOptionPane.INFORMATION_MESSAGE);
	}

	public void setupOntologies() {

		try {
			myManager = OWLManager.createOWLOntologyManager();
			System.out.println("Trying to load targetOntology");
			targetFile = new File(filePath);
			targetOntology = myManager.loadOntologyFromOntologyDocument(targetFile);

			axiomsT = new HashSet<>();
			axiomsTtmp = new HashSet<>();
			for (OWLAxiom axe : targetOntology.getAxioms())
				// removed !axe.toString().contains("Thing") &&
				if (axe.isOfType(AxiomType.SUBCLASS_OF) || axe.isOfType(AxiomType.EQUIVALENT_CLASSES)) {
					axiomsT.add(axe);
					axiomsTtmp.add(axe);
				}

			lastCE = null;

			// transfer Origin targetOntology to ManchesterOWLSyntaxOntologyFormat
			OWLOntologyFormat format = myManager.getOntologyFormat(targetOntology);
			ManchesterOWLSyntaxOntologyFormat manSyntaxFormat = new ManchesterOWLSyntaxOntologyFormat();
			if (format.isPrefixOWLOntologyFormat()) {
				manSyntaxFormat.copyPrefixesFrom(format.asPrefixOWLOntologyFormat());
			}

			// create personalized names for targetOntology
			ontologyFolderH = "src/main/resources/tmp/";
			ontologyFolder = "src/main/resources/tmp/";
			ontologyName = "";
			getOntologyName();

			// save ontologies
			newFile = new File(ontologyFolder);
			hypoFile = new File(ontologyFolderH);
			// save owl file as a new file in different location
			if (newFile.exists()) {
				newFile.delete();
			}
			newFile.createNewFile();
			myManager.saveOntology(targetOntology, manSyntaxFormat, IRI.create(newFile.toURI()));

			// Create OWL Ontology Manager for hypothesis and load hypothesis file
			if (hypoFile.exists()) {
				hypoFile.delete();
			}
			hypoFile.createNewFile();

			hypothesisOntology = myManager.loadOntologyFromOntologyDocument(hypoFile);

			System.out.println(targetOntology);
			System.out.println("Loaded successfully.");
			System.out.println();

			concepts = myMetrics.getSuggestionNames("concept", newFile);

			roles = myMetrics.getSuggestionNames("role", newFile);

			System.out.println("Total number of concepts is: " + concepts.size());
			System.out.println("Total number of roles is: " + roles.size());
			System.out.flush();
		} catch (OWLOntologyCreationException e) {
			System.out.println("Could not load targetOntology: " + e.getMessage());
		} catch (OWLException | IOException e) {
			e.printStackTrace();
		}

	}

	public void getOntologyName() {

		int con = 0;
		for (int i = 0; i < targetOntology.getOntologyID().toString().length(); i++)
			if (targetOntology.getOntologyID().toString().charAt(i) == '/')
				con = i;
		ontologyName = targetOntology.getOntologyID().toString().substring(con + 1,
				targetOntology.getOntologyID().toString().length());
		ontologyName = ontologyName.substring(0, ontologyName.length() - 3);
		if (!ontologyName.contains(".owl"))
			ontologyName = ontologyName + ".owl";
		ontologyFolder += ontologyName;
		ontologyFolderH += "hypo_" + ontologyName;
	}

	// --Commented out by Inspection START (30/04/2018, 15:27):
	// public Boolean equivalenceQuery() {
	//
	// return elQueryEngineForH.entailed(axiomsTtmp);
	// }
	// --Commented out by Inspection STOP (30/04/2018, 15:27)

	public OWLSubClassOfAxiom getCounterExample(ELEngine elQueryEngineForT, ELEngine elQueryEngineForH)
			throws Exception {
		// necessary to avoid Concurrent Modification Exception
		// Set<OWLAxiom> tmp = new HashSet<>(axiomsTtmp);

		Iterator<OWLAxiom> iterator = axiomsTtmp.iterator();
		// for (OWLAxiom selectedAxiom : tmp) {
		while (iterator.hasNext()) {
			OWLAxiom selectedAxiom = iterator.next();
			selectedAxiom.getAxiomType();

			// first get CounterExample from an axiom with the type SUBCLASS_OF
			if (selectedAxiom.isOfType(AxiomType.SUBCLASS_OF)) {
				if (!elQueryEngineForH.entailed(selectedAxiom)) {

					OWLSubClassOfAxiom counterexample = (OWLSubClassOfAxiom) selectedAxiom;
					return getCounterExampleSubClassOf(elQueryEngineForT, elQueryEngineForH, counterexample);
				}
				// axiomsTtmp.remove(selectedAxiom);
				iterator.remove();
			}
			if (selectedAxiom.isOfType(AxiomType.EQUIVALENT_CLASSES)) {
				OWLEquivalentClassesAxiom equivCounterexample = (OWLEquivalentClassesAxiom) selectedAxiom;
				Set<OWLSubClassOfAxiom> eqsubclassaxioms = equivCounterexample.asOWLSubClassOfAxioms();

				for (OWLSubClassOfAxiom subClassAxiom : eqsubclassaxioms) {
					if (!elQueryEngineForH.entailed(subClassAxiom)) {
						return getCounterExampleSubClassOf(elQueryEngineForT, elQueryEngineForH, subClassAxiom);
					}
				}
				// axiomsTtmp.remove(selectedAxiom);
				iterator.remove();
			}

		}
		throw new EquivalentException("No more counterexamples");
	}

	public OWLSubClassOfAxiom getCounterExampleSubClassOf(ELEngine elQueryEngineForT, ELEngine elQueryEngineForH,
			OWLSubClassOfAxiom counterexample) throws Exception {
		OWLSubClassOfAxiom newCounterexampleAxiom = counterexample;
		OWLClassExpression left = counterexample.getSubClass();
		OWLClassExpression right = counterexample.getSuperClass();

		if (oracleMerge) {
			newCounterexampleAxiom = elOracle.mergeLeft(left, right, MERGE_BOUND);
			left = newCounterexampleAxiom.getSubClass();
			right = newCounterexampleAxiom.getSuperClass();
		}

		if (oracleSaturate) {
			newCounterexampleAxiom = elOracle.saturateLeft(left, right, SATURATION_BOUND);
			left = newCounterexampleAxiom.getSubClass();
			right = newCounterexampleAxiom.getSuperClass();
		}

		if (oracleBranch) {
			newCounterexampleAxiom = elOracle.branchRight(left, right, BRANCH_BOUND);
			left = newCounterexampleAxiom.getSubClass();
			right = newCounterexampleAxiom.getSuperClass();
		}

		if (oracleLeftCompose) {
			newCounterexampleAxiom = elOracle.composeLeft(left, right, COMPOSE_LEFT_BOUND);
			left = newCounterexampleAxiom.getSubClass();
			right = newCounterexampleAxiom.getSuperClass();
		}

		if (oracleRightCompose) {
			newCounterexampleAxiom = elOracle.composeRight(left, right, COMPOSE_RIGHT_BOUND);
			left = newCounterexampleAxiom.getSubClass();
			right = newCounterexampleAxiom.getSuperClass();
		}

		if (oracleUnsaturate) {
			newCounterexampleAxiom = elOracle.unsaturateRight(left, right, UNSATURATE_BOUND);
		}

		return newCounterexampleAxiom;
	}

	
	public void precomputation(ELEngine elQueryEngineForT, ELEngine elQueryEngineForH) throws Exception {
		int i = elQueryEngineForT.getClassesInSignature().size();
		myMetrics.setMembCount(myMetrics.getMembCount() + i * (i - 1));
		for (OWLClass cl1 : elQueryEngineForT.getClassesInSignature()) {
			Set<OWLClass> implied = elQueryEngineForT.getSuperClasses(cl1, true);
			for (OWLClass cl2 : implied) {
				OWLSubClassOfAxiom addedAxiom = elQueryEngineForT.getSubClassAxiom(cl1, cl2);
				addHypothesis(addedAxiom);
			}
		}

	}
}
