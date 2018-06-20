package org.exactlearner.ui;

import java.awt.EventQueue;
import java.util.ArrayList;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextField;
import javax.swing.border.EmptyBorder;
import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;
import javax.swing.JTextArea;

public class ShowVocabulary extends JFrame {

	private JPanel contentPane;

	/**
	 * Launch the application.
	 */
	public static void main(String[] args) {
		EventQueue.invokeLater(new Runnable() {
			public void run() {
				try {
					ShowVocabulary frame = new ShowVocabulary(null, null);
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
	public ArrayList<String> concepts;
	public ArrayList<String> roles;
	
	public ShowVocabulary(ArrayList<String> concepts, ArrayList<String> roles) {
		
		this.concepts = concepts;
		this.roles = roles;
		
		setTitle("ExactLearner - Vocabulary");
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		setBounds(100, 100, 394, 306);
		contentPane = new JPanel();
		contentPane.setBorder(new EmptyBorder(5, 5, 5, 5));
		setContentPane(contentPane);
		contentPane.setLayout(null);
		
		JLabel lblNewLabel = new JLabel("Concepts");
		lblNewLabel.setBounds(10, 24, 146, 14);
		contentPane.add(lblNewLabel);
		
		JLabel lblNewLabel_1 = new JLabel("Roles");
		lblNewLabel_1.setBounds(229, 24, 139, 14);
		contentPane.add(lblNewLabel_1);
		
		JButton btnNewButton = new JButton("Back");
		btnNewButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				dispose();
			}
		});
		btnNewButton.setBounds(265, 232, 89, 23);
		contentPane.add(btnNewButton);
		
		
		JScrollPane scrollPane = new JScrollPane();
		scrollPane.setBounds(10, 49, 146, 149);
		contentPane.add(scrollPane);
		
		JTextArea textArea = new JTextArea();
		scrollPane.setViewportView(textArea);
		
		JScrollPane scrollPane_1 = new JScrollPane();
		scrollPane_1.setBounds(222, 49, 146, 149);
		contentPane.add(scrollPane_1);
		
		JTextArea textArea_1 = new JTextArea();
		scrollPane_1.setViewportView(textArea_1);
		for (int i=0; i<concepts.size();i++){

			textArea.setText(textArea.getText() + concepts.get(i) + "\n");
		}
		 
		for (int i=0; i<roles.size();i++){

			textArea_1.setText(textArea_1.getText() + roles.get(i) + "\n");
		}
		
	}

	public void populate()
	{
		
	}
}
