package org.exactlearner.ui;

import java.awt.EventQueue;
import java.awt.Image;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.border.EmptyBorder;
import javax.swing.JTextArea;

public class HelpInterface extends JFrame {

	private JPanel contentPane;

	public JButton nextButton;
	public JButton previousButton;
	public JLabel imgLabel;
	public int globalImg = 0;
	String[] imgList = {
						"src/main/resources/images/helpDifficulty.png",
						"src/main/resources/images/helpEquivalenceQuery.png",
						"src/main/resources/images/learnerSkills.png"
						};
	String[] descrList = {
						  "Oracle difficulty. This slider allows the user to select the difficulty for the oracle, if the value is "+
						  "set to 0, the oracle is disabled and counter examples will be simple. From then on, the higher the value the "+
						  "more complicated the counterexamples. Execution time will also increase.",
						  "Equivalence query. This button allows the user to ask if the hypothesis is equivalent fo the target ontology, "+
						  "in case it is, the user has constructed an equivalent ontology, in case it is not then the oracle returns a " +
						  "counterexample based on its difficulty, the counterexample is added to the hypothesis. Each time you ask one of "+
						  "these questions you will increase the no. of equivalence queries by 1.",
						  "Learner skills. The check boxes allow the user to select which skills the learner applies when generating counter models." +
						  " The more skills you select the longer it will take to complete the ontology."
						  };
	private JTextArea descrArea;
	
	/**
	 * Launch the application.
	 */
	public static void main(String[] args) {
		EventQueue.invokeLater(new Runnable() {
			public void run() {
				try {
					HelpInterface frame = new HelpInterface();
					frame.setVisible(true);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		});
	}

	/**
	 * Create the frame.
	 */
	public void populateHelp(int i)
	{
		ImageIcon icon = new ImageIcon(imgList[i]);
		Image img = icon.getImage();
		Image newImg = img.getScaledInstance(imgLabel.getWidth(), imgLabel.getHeight(), Image.SCALE_SMOOTH);
		ImageIcon newImc = new ImageIcon(newImg);
		descrArea.setText(descrList[i]);
		ImageIcon imgThisImg = new ImageIcon(imgList[i]);

		imgLabel.setIcon(imgThisImg);
		imgLabel.setIcon(newImc);
		globalImg = i;
	}
	public HelpInterface() {
		setTitle("ExactLearner - Help");
		setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
		setBounds(100, 100, 621, 429);
		contentPane = new JPanel();
		contentPane.setBorder(new EmptyBorder(5, 5, 5, 5));
		setContentPane(contentPane);
		contentPane.setLayout(null);

		previousButton = new JButton("Previous");
		previousButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				if(globalImg - 1 >= 0) {
					populateHelp(globalImg - 1);
					nextButton.setEnabled(true);
				}
				if(globalImg == 0)
					previousButton.setEnabled(false);
			}
		});
		previousButton.setEnabled(false);
		previousButton.setBounds(10, 356, 89, 23);
		contentPane.add(previousButton);

		nextButton = new JButton("Next");
		nextButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				if(globalImg + 1 <= 2) {
					populateHelp(globalImg + 1);
					previousButton.setEnabled(true);
				}
				if(globalImg == 2)
					nextButton.setEnabled(false);
			}
		});
		nextButton.setBounds(267, 356, 89, 23);
		contentPane.add(nextButton);

		JButton backButton = new JButton("Back");
		backButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				dispose();
			}
		});
		backButton.setBounds(506, 356, 89, 23);
		contentPane.add(backButton);
		
		imgLabel = new JLabel("New label");
		imgLabel.setBounds(54, 132, 512, 213);
		contentPane.add(imgLabel);
		
		descrArea = new JTextArea();
		descrArea.setWrapStyleWord(true);
		descrArea.setLineWrap(true);
		descrArea.setEditable(false);
		descrArea.setBounds(10, 11, 585, 95);
		contentPane.add(descrArea);

		populateHelp(0);
	}

}
