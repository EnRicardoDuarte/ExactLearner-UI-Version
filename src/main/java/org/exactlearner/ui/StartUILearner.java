package org.exactlearner.ui;

import java.awt.BorderLayout;
import java.awt.EventQueue;

import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.border.EmptyBorder;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JRadioButton;
import javax.swing.JButton;
import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;

public class StartUILearner extends JFrame {

	private JPanel contentPane;

	/**
	 * Launch the application.
	 */
	public static void main(String[] args) {
		EventQueue.invokeLater(new Runnable() {
			public void run() {
				try {
					StartUILearner frame = new StartUILearner();
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
	public StartUILearner() {
		setTitle("ExactLearner - Load");
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		setBounds(100, 100, 449, 251);
		contentPane = new JPanel();
		contentPane.setBorder(new EmptyBorder(5, 5, 5, 5));
		setContentPane(contentPane);
		contentPane.setLayout(null);
		
		JLabel lblNewLabel = new JLabel("Welcome to ExactLearner, a tool for learning EL ontologies!");
		lblNewLabel.setBounds(10, 11, 411, 14);
		contentPane.add(lblNewLabel);
		
		JLabel lblNewLabel_1 = new JLabel("Select a method for loading the ontology (must be EL) to learn:");
		lblNewLabel_1.setBounds(10, 54, 411, 14);
		contentPane.add(lblNewLabel_1);
		
		JRadioButton fromList = new JRadioButton("From list (Small ontologies only)");
		JRadioButton fromFile = new JRadioButton("From file (Opens explorer)");
		JButton btnNewButton = new JButton("Continue");
		btnNewButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				
			}
		});
		fromList.setBounds(6, 83, 415, 23);
		
		fromList.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent arg0) {
				fromFile.setSelected(false); 
				btnNewButton.setEnabled(true);
			}
		});
		contentPane.add(fromList);
		
		
		fromFile.setBounds(6, 109, 415, 23);
		fromFile.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent arg0) { 
				fromList.setSelected(false); 
				btnNewButton.setEnabled(true);
			}
		});
		contentPane.add(fromFile);
		
		btnNewButton.setEnabled(false);
		btnNewButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				int x = 0;
				if(fromList.isSelected())
					x = 0;
				if(fromFile.isSelected())
					x = 1; 
				wayToLoad way = new wayToLoad(x);
				
			}
		});
		btnNewButton.setBounds(10, 165, 89, 23);
		contentPane.add(btnNewButton);
		
		JButton btnNewButton_1 = new JButton("Exit");
		btnNewButton_1.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				System.exit(0);
			}
		});
		btnNewButton_1.setBounds(332, 165, 89, 23);
		contentPane.add(btnNewButton_1);
	}
	class wayToLoad implements ActionListener{
		
		int choice;
		public wayToLoad(int choice)
		{
			this.choice = choice;
			this.actionPerformed(null);
		}
		public void actionPerformed(ActionEvent event) {
			if(choice == 0){
				//System.out.println("from list");		 
				(new LoadFromList()).setVisible(true);
				dispose();
				
			} else if(choice == 1){
				//System.out.println("from file");
				(new LoadFromFile()).setVisible(true);
				dispose();
				
			}   else {
				JOptionPane.showMessageDialog(null, "Please choose one of the options to load an ontology.", "Alert", JOptionPane.INFORMATION_MESSAGE);
			}
			
		}
	}
}
